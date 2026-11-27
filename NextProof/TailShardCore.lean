import NextProof.TailPower16384
import NextProof.TailShardLight

namespace NextProof.Tail.Shards
open Polynomial

def window (k n : ℕ) := (projectedShiftInput16384.drop k).take n

def diag (k : ℕ) (d : ℤ) (g : List ℤ) :=
  diagonalFloor 65536 g k (2^100*(-131072)^k) d

structure Valid (p : Piece) (k : ℕ) : Prop where
  width : (window k p.n).length = p.n
  widthG : p.g.length = p.n
  input : horner (1+radix) (window k p.n) = p.inputVal
  output : horner radix p.g = p.outputVal
  inputBound : major 2 (window k p.n) = p.inputMajor
  outputBound : major 1 p.g = p.outputMajor
  floor : diag k p.firstDen p.g = p.q
  endD : endDen p.n k p.firstDen = p.afterDen

private theorem eval_app (x : ℤ) (a b : List ℤ) :
    horner x (a++b) = horner x a+x^a.length*horner x b := by
  induction a with
  | nil => simp [horner]
  | cons w a ih => simp only [List.cons_append,horner,ih,List.length_cons,pow_succ]; ring

private theorem light_input (N k c : ℕ) (ws : List ℤ) : Light.input N k c ws = shiftInput N k c ws := by
  induction ws generalizing k c with
  | nil => rfl
  | cons w ws ih => simp only [Light.input,shiftInput,centralNext,ih]

private theorem light_value (x : ℤ) (d : ℕ) (ws : List ℤ) : Light.value x d ws = horner x ws := by
  have slow (u : List ℤ) : Light.slow x u = horner x u := by
    induction u <;> simp [Light.slow,horner, *]
  induction d generalizing ws with
  | zero => exact slow ws
  | succ d ih =>
    rw [Light.value]
    split
    · exact slow ws
    · dsimp only
      rw [ih,ih]
      have h := eval_app x (ws.take (ws.length/2)) (ws.drop (ws.length/2))
      simpa [List.take_append_drop, Nat.min_eq_left (Nat.div_le_self _ _)] using h.symm

private theorem light_floor (ws : List ℤ) (j : ℕ) (m d : ℤ) :
    Light.floors ws j m d = diagonalFloor 65536 ws j m d := by
  induction ws generalizing j m d with
  | nil => rfl
  | cons w ws ih => simp only [Light.floors,diagonalFloor,ih]; rfl

theorem valid_of_checked {p : Piece} {k : ℕ} (h : Light.Checked p k) : Valid p k := by
  have hw : Light.window k p.n = window k p.n := by simp only [Light.window,window,projectedShiftInput16384,light_input]
  have hm (x : ℤ) (l : List ℤ) : horner x (l.map abs) = major x l := by
    induction l <;> simp [horner,major, *]
  exact ⟨hw ▸ h.width,h.widthG, by simpa only [light_value,hw] using h.input,
    by simpa only [light_value] using h.output, by simpa only [Int.natCast_natAbs,light_value,hm,hw] using h.inputBound,
    by simpa only [Int.natCast_natAbs,light_value,hm] using h.outputBound, by simpa only [diag,light_floor] using h.floor,h.endD⟩

private theorem major_app (x : ℤ) (a b : List ℤ) :
    major x (a++b) = major x a+x^a.length*major x b := by
  induction a with
  | nil => simp [major]
  | cons w a ih => simp only [List.cons_append,major,ih,List.length_cons,pow_succ]; ring

private theorem den_add (a b k : ℕ) (d : ℤ) :
    endDen (a+b) k d = endDen b (k+a) (endDen a k d) := by
  induction a generalizing k d with
  | zero => simp [endDen]
  | succ a ih =>
    rw [Nat.succ_add, endDen, endDen, ih]
    congr 1 <;> omega

private theorem diag_app (a b : List ℤ) (k : ℕ) (d : ℤ) :
    diag k d (a++b) = diag k d a ++ diag (k+a.length) (endDen a.length k d) b := by
  induction a generalizing k d with
  | nil => simp [diag, diagonalFloor,endDen]
  | cons w ws ih =>
    simp only [diag,List.cons_append,diagonalFloor,List.length_cons,endDen]
    apply congrArg (List.cons _)
    have eq : (2:ℤ)^100*(-131072)^k*(-2*65536)=2^100*(-131072)^(k+1) := by rw [pow_succ]; ring
    rw [eq]
    have ht := ih (k+1) (d*(2*k+1))
    rw [show k+1+ws.length = k+(ws.length+1) by omega] at ht
    exact ht

theorem join_valid {p q : Piece} {k : ℕ} (hp : Valid p k) (hq : Valid q (k+p.n))
    (hd : p.afterDen=q.firstDen) : Valid (join p q) k := by
  have hw : window k (p.n+q.n) = window k p.n ++ window (k+p.n) q.n := by
    simp only [window,List.take_add,List.drop_drop]
  constructor
  · change (window k (p.n+q.n)).length=_
    rw [hw,List.length_append,hp.width,hq.width]; rfl
  · simp only [join, List.length_append, hp.widthG, hq.widthG]
  · change horner _ (window k (p.n+q.n))=_
    rw [hw,eval_app,hp.input,hq.input,hp.width]; rfl
  · change horner _ (p.g++q.g)=_
    rw [eval_app,hp.output,hq.output,hp.widthG]
    simp only [join,radix,Int.shiftLeft_eq, ← pow_mul, mul_comm q.outputVal]
  · change major 2 (window k (p.n+q.n))=_
    rw [hw,major_app,hp.inputBound,hq.inputBound,hp.width]; rfl
  · change major 1 (p.g++q.g)=_
    simp only [major_app,hp.outputBound,hq.outputBound,one_pow,one_mul,join]
  · change diag k p.firstDen (p.g++q.g)=p.q++q.q
    rw [diag_app,hp.widthG,hp.endD,hd,hp.floor,hq.floor]
  · change endDen (p.n+q.n) k p.firstDen=q.afterDen
    rw [den_add,hp.endD,hd,hq.endD]

private theorem horner_coeff (a : List ℤ) (i : ℕ) :
    (horner (X : ℤ[X]) a).coeff i = a.getD i 0 := by
  induction a generalizing i with
  | nil => simp [horner,List.getD]
  | cons w ws ih =>
    rw [horner, ← C_eq_intCast, coeff_add]
    cases i with
    | zero => rw [coeff_C_zero, coeff_X_mul_zero, add_zero]; rfl
    | succ i => rw [coeff_C_succ, coeff_X_mul, zero_add, ih]; rfl

private theorem diag_take (n k : ℕ) (d m : ℤ) (g : List ℤ) :
    diagonalFloor 65536 (g.take n) k m d = (diagonalFloor 65536 g k m d).take n := by
  induction n generalizing k d m g with
  | zero => simp [diagonalFloor]
  | succ n ih => cases g <;> simp [diagonalFloor,ih]

/-- Exact equality to the published compact root, including all coefficient floors. -/
theorem root_eq {p : Piece} (hp : Valid p 0) (hn : p.n=projectedShiftInput16384.length)
    (hval : p.inputVal=p.outputVal) (hbound : p.inputMajor+p.outputMajor<radix)
    (hd : p.firstDen=baseDen) : powerLower = p.q.take 16385 := by
  have hw : window 0 p.n = projectedShiftInput16384 := by simp [window,hn]
  have hs : horner (C 1+X : ℤ[X]) projectedShiftInput16384 = horner X p.g := by
    apply shift_eq (B := radix) (by unfold radix; positivity)
    · rw [← hw,abs_one,one_add_one_eq_two,hp.inputBound,hp.outputBound]; exact hbound
    · rw [← hw,hp.input,hp.output,hval]
  have he : projectedTaylor=p.g := by
    apply List.ext_getElem
    · rw [hp.widthG,hn]
      exact (by simp only [projectedTaylor, fastShiftedVector_eq, shiftedVector, List.length_map,
        List.length_range, Blocks.size_eq, projectedBlocks, Blocks.balanced_list])
    · intro i hi hj
      have eq := congrArg (fun f : ℤ[X] => f.coeff i) (projected_shift.symm.trans hs)
      simpa [horner_coeff,List.getD,hi,hj] using eq
  have hf := hp.floor
  rw [diag,hd,pow_zero,mul_one] at hf
  rw [powerLower,he,diag_take,hf]

end NextProof.Tail.Shards
