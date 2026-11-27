import NextProof.TailTransform
import NextProof.TailModes
import NextProof.TailPacked
import Mathlib.Data.Nat.Log
import NextProof.ExteriorData16384
import NextProof.ExteriorSeries

/-! Signed diagonal scaling and exact integer inputs for the one-shift Laguerre transform. -/

namespace NextProof

open Polynomial

def laguerreOriginWeight (n : ℕ) : ℚ := (n.centralBinom : ℚ) / 4^n

def laguerreCoeffFactor (j : ℕ) : ℚ := (-4 : ℚ)^j * (j.factorial : ℚ) / ((2*j).factorial : ℚ)

private theorem factorial_even (j : ℕ) :
    (2*j).factorial = 2^j * j.factorial * Tail.oddFactor j := by
  induction j with
  | zero => simp [Tail.oddFactor]
  | succ j ih =>
    rw [Nat.mul_succ, Nat.factorial_succ (2*j+1), Nat.factorial_succ (2*j), ih,
      Nat.factorial_succ j, Tail.oddFactor, pow_succ]
    ring

theorem oddFactor_pos (j : ℕ) : 0 < Tail.oddFactor j := by
  induction j with
  | zero => decide
  | succ j ih => exact Nat.mul_pos (by omega) ih

theorem laguerreCoeffFactor_mul_oddFactor (j : ℕ) :
    laguerreCoeffFactor j * (Tail.oddFactor j : ℚ) = (-2 : ℚ)^j := by
  unfold laguerreCoeffFactor
  rw [factorial_even, show (-4 : ℚ) = -2*2 by norm_num, mul_pow]
  push_cast
  have hp : (Tail.oddFactor j : ℚ) ≠ 0 := by exact_mod_cast (oddFactor_pos j).ne'
  field_simp

noncomputable def laguerreGeneratingPolynomial (s : Finset ℕ) (w : ℕ → ℚ) : ℚ[X] :=
  ∑ n ∈ s, C (w n * laguerreOriginWeight n) * X^n

/-- Arbitrary finite rational weights in the factorial normalization. -/
theorem coeff_laguerre_sum_eq_shift (s : Finset ℕ) (w : ℕ → ℚ) (j : ℕ) :
    (∑ n ∈ s, C (w n) * laguerreHalf n).coeff j =
      laguerreCoeffFactor j * ((laguerreGeneratingPolynomial s w).comp (X+1)).coeff j := by
  have h := Tail.shifted_modes_coefficient s w id j
  simp only [id_eq] at h
  simp only [laguerreGeneratingPolynomial, laguerreOriginWeight, ← mul_div_assoc]
  rw [add_comm (X : ℚ[X]) 1]
  apply mul_left_cancel₀ (show (Tail.oddFactor j : ℚ) ≠ 0 by exact_mod_cast (oddFactor_pos j).ne')
  rw [← mul_assoc, mul_comm (Tail.oddFactor j : ℚ) (laguerreCoeffFactor j), laguerreCoeffFactor_mul_oddFactor]
  exact h

namespace Tail

/-- Cost-linear central binomial update with an exact natural-number division. -/
def centralNext (n c : ℕ) := (2*(2*n+1)*c)/(n+1)

theorem centralNext_correct (n : ℕ) :
    centralNext n n.centralBinom = (n+1).centralBinom := by
  rw [centralNext, ← Nat.succ_mul_centralBinom_succ, Nat.mul_div_cancel_left _ (by omega)]

/-- Integer coefficients of 4^(2N) F with zero odd powers, for an even-mode table.
The state `c` is the central binomial coefficient at degree `2*k`. -/
def shiftInput (N k c : ℕ) : List ℤ → List ℤ
  | [] => []
  | w::ws => w * c * 4^(2*N-2*k) :: 0 ::
      shiftInput N (k+1) (centralNext (2*k+1) (centralNext (2*k) c)) ws

/-- Direct integer-list API. A root certificate can supply a shifted integer list using
`shift_eq`. The only analytic polynomial here is the even-mode series in the conclusion. -/
theorem series_coeff_shiftInput (N k : ℕ) (ws : List ℤ) (j : ℕ) (hN : k + ws.length ≤ N+1) :
    (oddFactor j : ℚ) * (4:ℚ)^(2*N) * (series k ws).coeff j =
      (-2:ℚ)^j * (((X+1 : ℚ[X])^(2*k)) *
        horner (X+1 : ℚ[X]) (shiftInput N k (2*k).centralBinom ws)).coeff j := by
  induction ws generalizing k with
  | nil => simp [series, horner, shiftInput]
  | cons w ws ih =>
    have hk : k ≤ N := by simpa using (show k+1 ≤ N+1 by simp at hN; omega)
    have ht : k+1+ws.length ≤ N+1 := by simp at hN; omega
    have hc := coefficient_transform (2*k) j
    have hpow : (4:ℚ)^(2*N) = 4^(2*N-2*k) * 4^(2*k) := by
      rw [← pow_add]; congr 1; omega
    have hnext : centralNext (2*k+1) (centralNext (2*k) (2*k).centralBinom) =
        (2*(k+1)).centralBinom := by rw [centralNext_correct, centralNext_correct, Nat.mul_succ]
    rw [series, coeff_add, coeff_C_mul, mul_add, shiftInput, hnext, horner, horner]
    simp only [Int.cast_zero, zero_add]
    have split (u : ℤ) (p : ℚ[X]) :
        (X+1)^(2*k) * ((u : ℚ[X]) + (X+1)*((X+1)*p)) =
          C (u : ℚ)*(X+1)^(2*k) + (X+1)^(2*(k+1))*p := by
      rw [Nat.mul_succ, pow_add, C_eq_intCast]
      ring
    rw [split, coeff_add, coeff_C_mul, coeff_X_add_one_pow, mul_add, ← ih (k+1) ht]
    congr 1
    push_cast
    rw [hpow]
    field_simp at hc
    linear_combination (w : ℚ) * 4^(2*N-2*k) * hc

private theorem horner_map_rat (p : ℤ[X]) (v : List ℤ) :
    (horner p v).map (Int.castRingHom ℚ) = horner (p.map (Int.castRingHom ℚ)) v := by
  induction v with
  | nil => simp [horner]
  | cons a v ih => simp [horner, ih]

theorem horner_coeff_getD (v : List ℤ) (j : ℕ) :
    (horner (X : ℚ[X]) v).coeff j = (v.getD j 0 : ℚ) := by
  induction v generalizing j with
  | nil => simp [horner, List.getD]
  | cons a v ih =>
    rw [horner, ← C_eq_intCast, coeff_add]
    cases j with
    | zero => rw [coeff_C_zero, coeff_X_mul_zero, add_zero]; rfl
    | succ j => rw [coeff_C_succ, coeff_X_mul, zero_add, ih]; rfl

/-- Bind a checked shift to every coefficient of a real candidate's rational polynomial.
Integer inputs are low-to-high and the list may omit trailing zero coefficients. -/
theorem series_coeff_of_shift (N : ℕ) (ws v : List ℤ) (hN : ws.length ≤ N+1)
    (hshift : horner (C 1+X : ℤ[X]) (shiftInput N 0 1 ws) = horner X v) (j : ℕ) :
    (oddFactor j : ℚ) * (4:ℚ)^(2*N) * (series 0 ws).coeff j =
      (-2:ℚ)^j * (v.getD j 0 : ℚ) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) hshift
  simp only [horner_map_rat, Polynomial.map_add, Polynomial.map_one, map_one, map_X] at h
  change horner (1+X : ℚ[X]) (shiftInput N 0 1 ws) = horner X v at h
  have hs := series_coeff_shiftInput N 0 ws j (by simpa using hN)
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.centralBinom_zero, add_comm (X : ℚ[X]) 1] at hs
  rw [h, horner_coeff_getD] at hs
  exact hs

/-- The concrete integer inputs for the degree-16384 table in ExteriorData16384. -/
def projectedShiftInput16384 : List ℤ := shiftInput 8192 0 1 Exterior.Data16384.weights

/-- The table has 8193 even-mode weights. A checked translation binds all 16385 power
coefficients, with the common witness denominator supplied by ExteriorData16384. -/
theorem projected16384_coeff_of_shift (v : List ℤ)
    (hshift : horner (C 1+X : ℤ[X]) projectedShiftInput16384 = horner X v) (j : ℕ) :
    (oddFactor j : ℚ) * (4:ℚ)^16384 * (Exterior.Data16384.denominator : ℚ) *
        (C (1 / (Exterior.Data16384.denominator : ℚ)) * series 0 Exterior.Data16384.weights).coeff j =
      (-2:ℚ)^j * (v.getD j 0 : ℚ) := by
  have hlen : Exterior.Data16384.weights.length ≤ 8192+1 := by decide +kernel
  have hd : (Exterior.Data16384.denominator : ℚ) ≠ 0 := by
    unfold Exterior.Data16384.denominator
    positivity
  have h := series_coeff_of_shift 8192 _ v hlen hshift j
  rw [coeff_C_mul, ← h]
  generalize (4:ℚ)^16384 = b
  change _ * b * _ * (_ * _) = _ * b * _
  field_simp

/-- Direct balanced-integer checker interface for the degree-16384 JSON witness. -/
theorem projected16384_coeff_of_blocks (a b : Blocks) (B : ℤ)
    (ha : a.list = projectedShiftInput16384) (hB : 0 < B)
    (hb : a.absBlocks.subst 2 + b.absBlocks.subst 1 < B)
    (he : a.subst (1+B) = b.subst B) (j : ℕ) :
    (oddFactor j : ℚ) * (4:ℚ)^16384 * (Exterior.Data16384.denominator : ℚ) *
        (C (1 / (Exterior.Data16384.denominator : ℚ)) * series 0 Exterior.Data16384.weights).coeff j =
      (-2:ℚ)^j * (b.list.getD j 0 : ℚ) := by
  apply projected16384_coeff_of_shift
  rw [← ha]
  exact Blocks.shift a b 1 B hB (by simpa using hb) he

/-- Extract one signed radix digit with two balanced divisions. This allows random
access after a single packed evaluation has been shared across all coefficients. -/
def radixDigit (B j : ℕ) (v : ℤ) : ℤ := (v.bdiv (B^j)).bmod B

private lemma eval_split (p : ℤ[X]) (B : ℕ) :
    p.eval (B : ℤ) = p.coeff 0 + (B : ℤ) * p.divX.eval (B : ℤ) := by
  have h := congrArg (eval (B : ℤ)) (divX_mul_X_add p)
  simpa [mul_comm, add_comm] using h.symm

private lemma split_prefix (B j : ℕ) (hB : 0 < B) (p : ℤ[X])
    (hc : ∀ i, 2*|p.coeff i| < (B : ℤ)) :
    ∃ (lo : ℤ) (q : ℤ[X]), p.eval (B : ℤ) = lo + (B : ℤ)^j * q.eval (B : ℤ) ∧
      2*|lo| < (B : ℤ)^j ∧ q.coeff 0 = p.coeff j := by
  induction j generalizing p with
  | zero => exact ⟨0,p,by simp,by simp,rfl⟩
  | succ j ih =>
    obtain ⟨z,q,he,hz,hq⟩ := ih p.divX (fun i => by simpa [coeff_divX] using hc (i+1))
    refine ⟨p.coeff 0 + (B : ℤ)*z, q, ?_, ?_, by simpa [coeff_divX] using hq⟩
    · rw [eval_split p B, he, pow_succ]
      ring
    · have hb : (0 : ℤ) ≤ B := by positivity
      have h0 : 2*|p.coeff 0| ≤ (B : ℤ)-1 := by have := hc 0; omega
      have hz' : 2*|z| ≤ (B : ℤ)^j-1 := by omega
      calc
        2*|p.coeff 0 + (B : ℤ)*z| ≤ 2*(|p.coeff 0| + (B : ℤ)*|z|) := by
          gcongr
          simpa [abs_mul] using abs_add_le (p.coeff 0) ((B : ℤ)*z)
        _ ≤ (B : ℤ)^(j+1)-1 := by
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left hz' hb]
        _ < _ := by omega

private lemma balanced_low (B : ℕ) (lo hi : ℤ) (h : 2*|lo| < (B : ℤ)) :
    (lo + (B : ℤ)*hi).bmod B = lo := by
  rw [Int.add_mul_bmod_self_left]
  exact Int.bmod_eq_of_le_mul_two (by have := neg_abs_le lo; omega)
    (by have := le_abs_self lo; omega)

theorem radixDigit_eval (B j : ℕ) (hB : 0 < B) (p : ℤ[X])
    (hc : ∀ i, 2*|p.coeff i| < (B : ℤ)) :
    radixDigit B j (p.eval (B : ℤ)) = p.coeff j := by
  obtain ⟨lo,q,he,hlo,hq⟩ := split_prefix B j hB p hc
  have hb : (0 : ℤ) < (B^j : ℕ) := by exact_mod_cast Nat.pow_pos hB
  have hm := balanced_low (B^j) lo (q.eval (B : ℤ)) (by exact_mod_cast hlo)
  push_cast at hm
  have hd := Int.bdiv_add_bmod (p.eval (B : ℤ)) (B^j)
  push_cast at hd
  rw [he, hm] at hd
  have hh : (p.eval (B : ℤ)).bdiv (B^j) = q.eval (B : ℤ) := by
    apply mul_left_cancel₀ (show (B : ℤ)^j ≠ 0 by positivity)
    rw [he]
    linarith
  rw [radixDigit, hh, eval_split q B, balanced_low, hq]
  simpa [hq] using hc j

/-- One balanced evaluation of the input polynomial at radix plus one yields every
coefficient of the translated polynomial. The radix is chosen from a proved majorant. -/
def packedShiftRadix (v : List ℤ) : ℕ :=
  2 ^ ((2 * (major 2 v).natAbs).log2 + 1)

def packedShiftValue (v : List ℤ) : ℤ :=
  (Blocks.balanced (v.length.log2 + 1) v).subst (1 + (packedShiftRadix v : ℤ))

theorem packedShift_correct (v : List ℤ) (j : ℕ) :
    radixDigit (packedShiftRadix v) j (packedShiftValue v) =
      (horner (C 1+X : ℤ[X]) v).coeff j := by
  have h := horner_bound 1 v
  have hbound : 2*(major 2 v).natAbs < packedShiftRadix v := by
    simpa only [packedShiftRadix, Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (b:=2) (by decide) (2*(major 2 v).natAbs)
  have hv : packedShiftValue v = (horner (C 1+X : ℤ[X]) v).eval (packedShiftRadix v : ℤ) := by
    simp [packedShiftValue, Blocks.subst_eq, horner_eval]
  rw [hv]
  apply radixDigit_eval _ _ (by unfold packedShiftRadix; positivity)
  intro i
  have hi : |(horner (C 1+X : ℤ[X]) v).coeff i| ≤ major 2 v := by simpa using h i
  have hh : (2 : ℤ)*(major 2 v).natAbs < packedShiftRadix v := by exact_mod_cast hbound
  rw [Int.natCast_natAbs] at hh
  have := le_abs_self (major 2 v)
  omega

private theorem coeff_horner_shift_cast (v : List ℤ) (j : ℕ) :
    (((horner (C 1+X : ℤ[X]) v).coeff j : ℤ) : ℚ) =
      (horner (1+X : ℚ[X]) v).coeff j := by
  have h := horner_map_rat (1+X : ℤ[X]) v
  simp only [Polynomial.map_add, Polynomial.map_one, map_X] at h
  have h' := congrArg (fun p : ℚ[X] => p.coeff j) h
  simpa only [C_1, coeff_map, Int.coe_castRingHom] using h'

theorem series_coeff_packed (N D : ℕ) (hD : 0 < D) (ws : List ℤ) (hN : ws.length ≤ N+1) (j : ℕ) :
    (oddFactor j : ℚ) * (4:ℚ)^(2*N) * (D : ℚ) *
        (C (1 / (D : ℚ)) * series 0 ws).coeff j =
      (-2:ℚ)^j * (radixDigit (packedShiftRadix (shiftInput N 0 1 ws)) j
        (packedShiftValue (shiftInput N 0 1 ws)) : ℚ) := by
  rw [packedShift_correct, coeff_horner_shift_cast]
  have hs := series_coeff_shiftInput N 0 ws j (by simpa using hN)
  simp only [Nat.mul_zero, Nat.centralBinom_zero, pow_zero, one_mul, add_comm (X : ℚ[X]) 1] at hs
  rw [coeff_C_mul, ← hs]
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

/-- Unconditional, executable random-access coefficient formula for the full degree-16384
witness. The same packed integer serves all indices. -/
theorem projected16384_coeff_packed (j : ℕ) :
    (oddFactor j : ℚ) * (4:ℚ)^16384 * (Exterior.Data16384.denominator : ℚ) *
        (C (1 / (Exterior.Data16384.denominator : ℚ)) * series 0 Exterior.Data16384.weights).coeff j =
      (-2:ℚ)^j * (radixDigit (packedShiftRadix projectedShiftInput16384) j
        (packedShiftValue projectedShiftInput16384) : ℚ) :=
  series_coeff_packed 8192 Exterior.Data16384.denominator (by decide +kernel)
    Exterior.Data16384.weights (by decide +kernel) j

/-- Euclidean integer division gives a lower bound for the scaled coefficient even
when its numerator is negative. -/
theorem floor_scaledCoeff_le (d s R v : ℤ) (j : ℕ) (x : ℚ) (hd : 0 < d)
    (h : (d : ℚ)*x = (-2:ℚ)^j*(v : ℚ)) :
    (((s*(-2*R)^j*v / d : ℤ) : ℚ)) ≤ (s : ℚ) * (R : ℚ)^j * x := by
  apply (mul_le_mul_iff_of_pos_right (show 0 < (d : ℚ) by exact_mod_cast hd)).mp
  calc
    _ ≤ ((s*(-2*R)^j*v : ℤ) : ℚ) := by exact_mod_cast Int.ediv_mul_le _ hd.ne'
    _ = _ := by
      push_cast
      rw [mul_pow]
      linear_combination -(s : ℚ)*(R : ℚ)^j*h

theorem series_eq_exterior (k : ℕ) (ws : List ℤ) : series k ws = Exterior.series k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => rw [series, Exterior.series, ih]

/-- Exact scalar floor used by the compact root with radius 65536 and 100 binary digits. -/
def rootFloor16384 (j : ℕ) (v : ℤ) : ℤ :=
  (2^100 * (-2*65536 : ℤ)^j * v) /
    ((oddFactor j : ℤ) * 4^16384 * Exterior.Data16384.denominator)

theorem rootFloor16384_le (j : ℕ)
    (v : ℤ) (hv : v = radixDigit (packedShiftRadix projectedShiftInput16384) j
      (packedShiftValue projectedShiftInput16384)) :
    (rootFloor16384 j v : ℚ) ≤ 2^100*(65536 : ℚ)^j *
      (Exterior.witness Exterior.Data16384.denominator Exterior.Data16384.weights).coeff j := by
  have h := projected16384_coeff_packed j
  rw [← hv, series_eq_exterior] at h
  have hD : 0 < Exterior.Data16384.denominator := by decide +kernel
  have hf := floor_scaledCoeff_le
    ((oddFactor j : ℤ) * 4^16384 * Exterior.Data16384.denominator) (2^100) 65536 v j
    ((Exterior.witness Exterior.Data16384.denominator Exterior.Data16384.weights).coeff j)
    (by have := oddFactor_pos j; positivity) (by
      push_cast
      exact h)
  simpa only [rootFloor16384, Int.cast_pow, Int.cast_ofNat] using hf

end Tail
end NextProof

#print axioms NextProof.coeff_laguerre_sum_eq_shift
#print axioms NextProof.Tail.series_coeff_shiftInput
#print axioms NextProof.Tail.projected16384_coeff_of_blocks
#print axioms NextProof.Tail.projected16384_coeff_packed
#print axioms NextProof.Tail.rootFloor16384_le
