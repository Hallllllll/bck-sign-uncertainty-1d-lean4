import NextProof.TailDecode
import NextProof.LaguerreCoeffs
import NextProof.ExteriorTailBinding

namespace NextProof.Tail
open Polynomial

/-- Balanced representation of the generating polynomial F at the shared scale. -/
def projectedBlocks : Blocks := Blocks.balanced 15 projectedShiftInput16384

def projectedTaylor : List ℤ := fastShiftedVector 15 projectedBlocks

theorem projected_shift :
    horner (C 1+X : ℤ[X]) projectedShiftInput16384 = horner X projectedTaylor := by
  simpa only [projectedTaylor, fastShiftedVector_eq, projectedBlocks, Blocks.balanced_list] using
    shiftedVector_identity projectedBlocks

theorem projected_coefficient (j : ℕ) :
    (oddFactor j : ℚ) * (4:ℚ)^16384 * (Exterior.Data16384.denominator : ℚ) *
        Exterior.projected16384.coeff j =
      (-2:ℚ)^j * (projectedTaylor.getD j 0 : ℚ) := by
  rw [Exterior.projected16384_eq_tail_series]
  exact projected16384_coeff_of_shift _ projected_shift j

/-- Floor a sequence of exact Taylor coefficients with varying diagonal factors.
The factors advance by small integer multiplications, including the sign. -/
def diagonalFloor (R : ℤ) : List ℤ → ℕ → ℤ → ℤ → List ℤ
  | [], _, _, _ => []
  | a::as, j, m, d => (a*m/d)::diagonalFloor R as (j+1) (m*(-2*R)) (d*(2*j+1))

theorem diagonalFloor_length (R : ℤ) (xs : List ℤ) (j : ℕ) (m d : ℤ) :
    (diagonalFloor R xs j m d).length = xs.length := by
  induction xs generalizing j m d <;> simp [diagonalFloor, *]

private theorem diagonalFloor_get (R : ℤ) (xs : List ℤ) (j i : ℕ) (m d : ℤ) (hi : i < xs.length) :
    (diagonalFloor R xs j (m*(-2*R)^j) (d*(oddFactor j : ℤ))).getD i 0 =
    xs.getD i 0 * (m*(-2*R)^(j+i)) / (d*(oddFactor (j+i) : ℤ)) := by
  induction xs generalizing j i with
  | nil => simp at hi
  | cons w xs ih =>
    cases i with
    | zero => simp [diagonalFloor, List.getD]
    | succ i =>
      change (diagonalFloor R xs (j+1) _ _).getD i 0 = _
      have hd : d*(oddFactor j : ℤ)*(2*(j : ℤ)+1) = d*(oddFactor (j+1) : ℤ) := by
        rw [oddFactor]; push_cast; ring
      rw [hd, mul_assoc, ← pow_succ, ih (j+1) i (by simpa using hi),
        show j+1+i = j+(i+1) by omega]
      rfl

def baseDen : ℤ := 4^16384*(Exterior.Data16384.denominator : ℤ)

/-- Coefficientwise lower integer polynomial for 2^100 P(65536 z), in
ascending degree, with the 16385 coefficients used by the compact tree. -/
def powerLower : List ℤ :=
  diagonalFloor 65536 (projectedTaylor.take 16385) 0 (2^100) baseDen

private theorem source_length (k N c : ℕ) (ws : List ℤ) :
    (shiftInput N k c ws).length = 2*ws.length := by
  induction ws generalizing k c with
  | nil => rfl
  | cons w ws ih =>
    simp only [shiftInput, List.length_cons, ih]
    omega

private theorem taylor_length : projectedTaylor.length = 16386 := by
  simp only [projectedTaylor, fastShiftedVector_eq, shiftedVector, List.length_map, List.length_range,
    Blocks.size_eq, projectedBlocks, Blocks.balanced_list, projectedShiftInput16384, source_length]
  decide +kernel

theorem powerLower_length : powerLower.length = 16385 := by
  rw [powerLower, diagonalFloor_length, List.length_take, taylor_length]; decide

theorem powerLower_coeff (i : ℕ) (hi : i < 16385) :
    ((powerLower.getD i 0 : ℤ) : ℚ) ≤
      (2:ℚ)^100 * 65536^i * Exterior.projected16384.coeff i := by
  have hi' : i < (projectedTaylor.take 16385).length := by
    rw [List.length_take,taylor_length]; exact hi
  have h := diagonalFloor_get 65536 (projectedTaylor.take 16385) 0 i ((2:ℤ)^100) baseDen hi'
  simp only [pow_zero, mul_one, oddFactor, Nat.cast_one, zero_add] at h
  change powerLower.getD i 0 = _ at h
  have hg : (projectedTaylor.take 16385).getD i 0 = projectedTaylor.getD i 0 := by
    simp [List.getD, hi]
  rw [hg] at h
  have hd : (0 : ℤ) < baseDen*(oddFactor i : ℤ) := by
    have := oddFactor_pos i
    unfold baseDen Exterior.Data16384.denominator
    positivity
  have bound := Int.ediv_mul_le (projectedTaylor.getD i 0 * ((2:ℤ)^100*(-2*65536)^i)) hd.ne'
  rw [← h] at bound
  have bound' := (show ((powerLower.getD i 0 : ℤ) : ℚ) * ((baseDen*(oddFactor i : ℤ) : ℤ) : ℚ) ≤
    ((projectedTaylor.getD i 0 * ((2:ℤ)^100*(-2*65536)^i) : ℤ) : ℚ) by exact_mod_cast bound)
  apply le_of_mul_le_mul_right (a := ((baseDen*(oddFactor i : ℤ) : ℤ) : ℚ)) _ (by exact_mod_cast hd)
  refine bound'.trans_eq ?_
  have hc := projected_coefficient i
  unfold baseDen
  push_cast
  rw [show (-131072 : ℚ)^i = (-2:ℚ)^i * 65536^i by rw [← mul_pow]; norm_num]
  linear_combination -(2:ℚ)^100 * 65536^i * hc

private theorem lag_degree (n : ℕ) : (laguerreHalf n).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have h := coefficient_transform n j
  rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (oddFactor_pos j).ne')

private theorem series_degree (ws : List ℤ) (j N : ℕ) (hj : j+ws.length ≤ N+1) :
    (series j ws).natDegree ≤ 2*N := by
  induction ws generalizing j with
  | nil => simp [series]
  | cons w ws ih =>
    rw [series]
    apply natDegree_add_le_of_degree_le
    · apply (natDegree_C_mul_le ..).trans
      apply (lag_degree _).trans
      simp only [List.length_cons] at hj
      omega
    · exact ih (j+1) (by simp only [List.length_cons] at hj; omega)

private theorem witness_degree : Exterior.projected16384.natDegree < 16385 := by
  rw [Exterior.projected16384_eq_tail_series]
  apply Nat.lt_succ_of_le
  exact (natDegree_C_mul_le ..).trans
    (series_degree _ 0 8192 (by decide +kernel))

private theorem horner_sum (xs : List ℤ) (x : ℝ) :
    horner x xs = ∑ i ∈ Finset.range xs.length, ((xs.getD i 0 : ℤ) : ℝ)*x^i := by
  induction xs with
  | nil => simp [horner]
  | cons a xs ih =>
    rw [horner, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero,mul_one,List.getD_cons_zero,List.getD_cons_succ, pow_succ]
    ring_nf

/-- Root interface for the compact certificate. The inequality is valid on all
nonnegative arguments. -/
theorem powerLower_le (z : ℝ) (hz : 0 ≤ z) :
    horner z powerLower ≤ (2:ℝ)^100 * Exterior.projected16384.eval₂ (algebraMap ℚ ℝ) (65536*z) := by
  rw [horner_sum, powerLower_length, eval₂_eq_sum_range' _ witness_degree, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := powerLower_coeff i (Finset.mem_range.mp hi)
  have h' : ((powerLower.getD i 0 : ℤ) : ℝ) ≤
      (2:ℝ)^100*65536^i*(Exterior.projected16384.coeff i : ℝ) := by exact_mod_cast h
  refine (mul_le_mul_of_nonneg_right h' (pow_nonneg hz i)).trans_eq ?_
  rw [mul_pow]
  change _ = (2:ℝ)^100 * ((Exterior.projected16384.coeff i : ℝ) * (65536^i * z^i))
  ring

end NextProof.Tail
#print axioms NextProof.Tail.powerLower_le
