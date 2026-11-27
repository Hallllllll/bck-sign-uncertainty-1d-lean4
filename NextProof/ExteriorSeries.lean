import NextProof.ExteriorRatio

namespace NextProof.Exterior

open Polynomial
open scoped FourierTransform

set_option maxRecDepth 4096

/-- The weights are in increasing order. Entry j multiplies the mode of index 2*j. -/
noncomputable def series (j : ℕ) : List ℤ → ℚ[X]
  | [] => 0
  | w :: ws => C (w : ℚ) * laguerreHalf (2*j) + series (j+1) ws

noncomputable def witness (den : ℕ) (ws : List ℤ) : ℚ[X] :=
  C (1 / (den : ℚ)) * series 0 ws

theorem series_append (j : ℕ) (a b : List ℤ) :
    series j (a ++ b) = series j a + series (j+a.length) b := by
  induction a generalizing j with
  | nil => simp [series]
  | cons u a ih =>
    rw [List.cons_append, series, series, ih]
    simp only [List.length_cons]
    rw [show j + 1 + a.length = j + (a.length + 1) by omega, add_assoc]

theorem eval_series_cons (j : ℕ) (w : ℤ) (ws : List ℤ) (x : ℝ) :
    (series j (w::ws)).eval₂ (algebraMap ℚ ℝ) x =
      (w : ℝ)*mode (2*j) x + (series (j+1) ws).eval₂ (algebraMap ℚ ℝ) x := by
  rw [series, eval₂_add, eval₂_mul, eval₂_C, map_intCast, mode]

theorem eval_witness (den : ℕ) (ws : List ℤ) (x : ℝ) :
    (witness den ws).eval₂ (algebraMap ℚ ℝ) x =
      (1 / (den : ℝ)) * (series 0 ws).eval₂ (algebraMap ℚ ℝ) x := by
  simp [witness]

theorem series_fourier (j : ℕ) (ws : List ℤ) :
    𝓕 (radialGaussian (series j ws)) = radialGaussian (series j ws) := by
  induction ws generalizing j with
  | nil =>
    simpa [series] using fourier_evenLaguerre_sum (∅ : Finset ℕ) (fun _ => (0 : ℚ)) id
  | cons w ws ih =>
    rw [series, radialGaussian_add, fourier_add (integrable_radialGaussian _) (integrable_radialGaussian _),
      ih, radialGaussian_C_mul, fourier_const_mul, fourier_laguerreHalf, pow_mul]
    simp

theorem witness_fourier (den : ℕ) (ws : List ℤ) :
    𝓕 (radialGaussian (witness den ws)) = radialGaussian (witness den ws) := by
  rw [witness, radialGaussian_C_mul, fourier_const_mul, series_fourier]

/-- Sum of the absolute values of the negative weights. -/
def negativeMass (ws : List ℤ) : ℤ := (ws.map (fun w => max 0 (-w))).sum

theorem negativeMass_append (a b : List ℤ) :
    negativeMass (a ++ b) = negativeMass a + negativeMass b := by
  simp [negativeMass]

private theorem low_bound (x : ℝ) (hx : 65536 ≤ x) (j : ℕ) (ws : List ℤ)
    (hj : j+ws.length ≤ 4611) :
    -(negativeMass ws : ℝ)*((3/4 : ℝ)^64*positiveMode 16384 x) ≤
      (series j ws).eval₂ (algebraMap ℚ ℝ) x := by
  have hx' : 4*(16384 : ℝ) ≤ x := by norm_num; linarith
  induction ws generalizing j with
  | nil => simp [negativeMass, series]
  | cons w ws ih =>
    have hj' : j ≤ 4610 := by simp only [List.length_cons] at hj; omega
    have htail := ih (j+1) (by simp only [List.length_cons] at hj; omega)
    have hD : 0 < (16384 : ℕ) := by decide
    have hpos := (positiveMode_pos hD (show 2*j ≤ 16384 by omega) hx').le
    have h₁ : positiveMode (2*j) x ≤ positiveMode 9220 x :=
      positiveMode_mono hD (by omega) (by decide) hx'
    have h₂ : positiveMode 9220 x ≤ (3/4 : ℝ)^64*positiveMode (9220+64) x :=
      positiveMode_block hD (by decide) (by norm_num) hx'
    have h₃ : positiveMode (9220+64) x ≤ positiveMode 16384 x :=
      positiveMode_mono hD (by decide) (by decide) hx'
    have hbd := (h₁.trans h₂).trans (mul_le_mul_of_nonneg_left h₃ (by positivity))
    have hwterm :
        -(max 0 (-w) : ℤ) * ((3/4 : ℝ)^64*positiveMode 16384 x) ≤
          (w : ℝ)*positiveMode (2*j) x := by
      by_cases hw : 0 ≤ w
      · rw [max_eq_left (by omega : -w ≤ 0)]
        push_cast
        simp only [neg_zero, zero_mul]
        exact mul_nonneg (by exact_mod_cast hw) hpos
      · rw [max_eq_right (by omega : 0 ≤ -w)]
        push_cast
        simp only [neg_neg]
        exact mul_le_mul_of_nonpos_left hbd (by exact_mod_cast (show w ≤ 0 by omega))
    rw [eval_series_cons, mode_even_eq]
    have hmass : negativeMass (w::ws) = max 0 (-w) + negativeMass ws := rfl
    rw [hmass, Int.cast_add]
    convert add_le_add hwterm htail using 1
    ring

private theorem high_nonneg (x : ℝ) (hx : 65536 ≤ x) (j : ℕ) (ws : List ℤ)
    (hj : j+ws.length ≤ 8192) (hw : ws.all (fun w => decide (0 ≤ w)) = true) :
    0 ≤ (series j ws).eval₂ (algebraMap ℚ ℝ) x := by
  have hx' : 4*(16384 : ℝ) ≤ x := by norm_num; linarith
  induction ws generalizing j with
  | nil => simp [series]
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [List.length_cons] at hj
    rw [eval_series_cons, mode_even_eq]
    exact add_nonneg
      (mul_nonneg (by exact_mod_cast hw.1)
        (positiveMode_pos (by decide : 0 < (16384 : ℕ)) (show 2*j ≤ 16384 by omega) hx').le)
      (ih (j+1) (by omega) hw.2)

/-- A fixed-size tail certificate, using a 64-step ratio block above the low weights. -/
theorem far_positive (den : ℕ) (lo hi : List ℤ) (lead : ℤ)
    (hd : 0 < den) (hl : lo.length = 4611) (hh : hi.length = 3581)
    (ha : hi.all (fun w => decide (0 ≤ w)) = true)
    (hm : negativeMass lo ≤ 2^96) (ht : 2^74 ≤ lead)
    (x : ℝ) (hx : 65536 ≤ x) :
    0 < (witness den ((lo ++ hi) ++ [lead])).eval₂ (algebraMap ℚ ℝ) x := by
  have hx' : 4*(16384 : ℝ) ≤ x := by norm_num; linarith
  have hp := positiveMode_pos (by decide : 0 < (16384 : ℕ)) (show 16384 ≤ 16384 by decide) hx'
  have hlow := low_bound x hx 0 lo (by omega)
  have hhigh := high_nonneg x hx 4611 hi (by omega) ha
  have hc : (2 : ℝ)^96*(3/4 : ℝ)^64 < 2^74 := by norm_num
  have hm' : (negativeMass lo : ℝ) ≤ (2 : ℝ)^96 := by exact_mod_cast hm
  have hmass := mul_le_mul_of_nonneg_right hm' (show 0 ≤ (3/4 : ℝ)^64 by positivity)
  have hlead : (2 : ℝ)^74 ≤ lead := by exact_mod_cast ht
  have hg : 0 < ((lead : ℝ) - (negativeMass lo : ℝ)*(3/4 : ℝ)^64) * positiveMode 16384 x :=
    mul_pos (sub_pos.mpr ((hmass.trans_lt hc).trans_le hlead)) hp
  rw [eval_witness]
  apply mul_pos (by positivity)
  rw [series_append, series_append]
  simp only [List.length_append, hl, hh, zero_add, show 4611+3581 = 8192 by decide,
    eval₂_add]
  rw [eval_series_cons, mode_even_eq]
  simp only [series, eval₂_zero, add_zero] 
  change 0 < (series 0 lo).eval₂ (algebraMap ℚ ℝ) x +
    (series 4611 hi).eval₂ (algebraMap ℚ ℝ) x + (lead : ℝ)*positiveMode 16384 x
  apply hg.trans_le
  convert add_le_add_right (add_le_add hlow hhigh) ((lead : ℝ)*positiveMode 16384 x) using 1 <;> ring

end NextProof.Exterior
