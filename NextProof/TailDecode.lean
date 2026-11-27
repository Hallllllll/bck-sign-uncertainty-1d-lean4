import NextProof.TailDigits

namespace NextProof.Tail
open Polynomial

/-- Split signed limbs into two contiguous blocks at a time. This avoids one
full-width integer division for each of the 16385 output coefficients. -/
def decode (B : ℤ) : ℕ → ℕ → ℤ → List ℤ
  | 0, n, z => (List.range n).map (packedDigit B z)
  | d+1, n, z =>
    if n ≤ 1 then (List.range n).map (packedDigit B z)
    else
      let k := n/2
      let b := B^k
      decode B d k (lowerPart b z) ++ decode B d (n-k) (upperPart b z)

private theorem bound_value (B : ℤ) (hB : 0 < B) (ws : List ℤ)
    (hb : ∀ w ∈ ws, 2*|w| < B) : 2*|horner B ws| < B^ws.length := by
  induction ws with
  | nil => simp [horner]
  | cons w ws ih =>
    have h := ih (fun v hv => hb v (List.mem_cons_of_mem _ hv))
    have hw := hb w (List.mem_cons_self ..)
    have ha := abs_add_le w (B*horner B ws)
    rw [abs_mul, abs_of_pos hB] at ha
    have hh := mul_le_mul_of_nonneg_left (show 2*|horner B ws| ≤ B^ws.length - 1 by omega) hB.le
    simp only [horner, Int.cast_id, List.length_cons, pow_succ]
    linarith only [ha,hh,hw]

private theorem value_append (B : ℤ) (u v : List ℤ) :
    horner B (u++v) = horner B u + B^u.length * horner B v := by
  induction u with
  | nil => simp [horner]
  | cons w ws ih => simp only [List.cons_append,horner,ih,List.length_cons,pow_succ]; ring

private theorem coeffH (ws : List ℤ) (i : ℕ) : (horner (X : ℤ[X]) ws).coeff i = ws.getD i 0 := by
  induction ws generalizing i with
  | nil => simp [horner,List.getD]
  | cons a as ih =>
    rw [horner, ← C_eq_intCast, coeff_add]
    cases i with
    | zero => rw [coeff_C_zero, coeff_X_mul_zero, add_zero]; rfl
    | succ i => rw [coeff_C_succ, coeff_X_mul, zero_add, ih]; rfl

private theorem read_all (B : ℤ) (hB : 0 < B) (xs : List ℤ) (hb : ∀ x ∈ xs, 2*|x| < B) :
    (List.range xs.length).map (packedDigit B (horner B xs)) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range]
  have h : ∀ i, 2*|(horner (X : ℤ[X]) xs).coeff i| < B := by
    intro j
    rw [coeffH]
    by_cases hj : j < xs.length
    · simpa [List.getD, hj] using hb xs[j] (List.getElem_mem ..)
    · simpa [List.getD,hj] using hB
  have e := packedDigit_eval (horner (X : ℤ[X]) xs) B hB h i
  simpa [horner_eval, coeffH, List.getD, hi'] using e

theorem decode_eval (B : ℤ) (hB : 0 < B) (d : ℕ) (xs : List ℤ)
    (hb : ∀ x ∈ xs, 2*|x| < B) :
    decode B d xs.length (horner B xs) = xs := by
  induction d generalizing xs with
  | zero => exact read_all _ hB _ hb
  | succ d ih =>
    rw [decode]
    split
    · exact read_all _ hB _ hb
    · let k := xs.length/2
      let u := xs.take k
      let v := xs.drop k
      have huv : u++v=xs := List.take_append_drop ..
      have hl : u.length=k := by simp [u,k,Nat.min_eq_left (Nat.div_le_self _ _)]
      have hr : v.length=xs.length-k := by simp [v]
      have hu : ∀ x ∈ u, 2*|x| < B := fun x hx => hb x (by rw [← huv]; exact List.mem_append_left _ hx)
      have hv : ∀ x ∈ v, 2*|x| < B := fun x hx => hb x (by rw [← huv]; exact List.mem_append_right _ hx)
      have bp : 0 < B^k := pow_pos hB _
      have bound := bound_value B hB u hu
      rw [hl] at bound
      have he := value_append B u v
      rw [huv, hl] at he
      have hn := neg_abs_le (horner B u)
      have hp := le_abs_self (horner B u)
      have h0 : 0 ≤ horner B u + B^k/2 := by omega
      have hm : horner B u + B^k/2 < B^k := by omega
      have e : horner B xs + B^k/2 = (horner B u + B^k/2) + B^k * horner B v := by rw [he]; ring
      change decode B d k (lowerPart (B^k) _) ++ decode B d (xs.length-k) (upperPart (B^k) _) = xs
      rw [lowerPart, upperPart, e, Int.add_mul_ediv_left _ _ bp.ne',
        Int.ediv_eq_zero_of_lt h0 hm, zero_add, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt h0 hm, add_sub_cancel_right, ← hl, show xs.length-u.length=v.length by omega,
        ih u hu, ih v hv, huv]

def fastShiftedVector (d : ℕ) (a : Blocks) : List ℤ :=
  let B := radix a
  decode B d a.size (a.subst (1+B))

theorem fastShiftedVector_eq (d : ℕ) (a : Blocks) :
    fastShiftedVector d a = shiftedVector a := by
  let xs := shiftedVector a
  have hl : xs.length=a.size := by simp [xs,shiftedVector]
  have id := shiftedVector_identity a
  have eqv := congrArg (eval (radix a)) id
  simp only [horner_eval, eval_add, eval_C, eval_X, ← Blocks.subst_eq] at eqv
  have he : a.subst (1+radix a) = horner (radix a) xs := by
    simpa only [Blocks.subst_eq, Int.cast_one] using eqv
  have hb := horner_bound 1 a.list
  have hsize := radix_big a
  rw [Blocks.major_eq] at hsize
  change decode (radix a) d a.size (a.subst (1+radix a)) = xs
  rw [he, ← hl]
  apply decode_eval _ (by unfold radix; positivity)
  intro w hw
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hw
  change i < xs.length at hi
  have h := hb i
  rw [id, coeffH] at h
  change |xs.getD i 0| ≤ _ at h
  simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some, eq, abs_one, one_add_one_eq_two] at h
  linarith

end NextProof.Tail
