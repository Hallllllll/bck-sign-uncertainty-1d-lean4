import NextProof.Fourier
import NextProof.Data
import Mathlib.Analysis.Real.Pi.Bounds

namespace NextProof

open MeasureTheory Polynomial Set
open scoped FourierTransform

/-- Products of valid physical radii for the dimension-one BCK plus class.
The Fourier transform uses Lebesgue measure and the exp(-2πixξ) convention.
Real-valuedness is required globally for both functions. -/
def radiusProducts : Set ℝ :=
  {v | ∃ (f : ℝ → ℂ) (r s : ℝ), 0 ≤ r ∧ 0 ≤ s ∧ v = r*s ∧
    Continuous f ∧ Integrable f ∧ Integrable (𝓕 f) ∧ f ≠ 0 ∧
    (∀ x, f (-x) = f x) ∧ (∀ x, (f x).im = 0 ∧ (𝓕 f x).im = 0) ∧
    (f 0).re ≤ 0 ∧ (𝓕 f 0).re ≤ 0 ∧
    (∀ x : ℝ, r ≤ |x| → 0 ≤ (f x).re) ∧
    (∀ x : ℝ, s ≤ |x| → 0 ≤ (𝓕 f x).re)}

noncomputable def AplusSquared : ℝ := sInf radiusProducts

/-- A self-Fourier half-line certificate gives a bound in physical coordinates. -/
theorem upper_from_polynomial (p : ℚ[X]) (t : ℝ) (ht : 0 < t)
    (hself : 𝓕 (radialGaussian p) = radialGaussian p)
    (hnonzero : radialGaussian p ≠ 0) (horigin : p.eval₂ (algebraMap ℚ ℝ) 0 ≤ 0)
    (htail : ∀ z : ℝ, t ≤ z → 0 ≤ p.eval₂ (algebraMap ℚ ℝ) z) :
    AplusSquared ≤ t / (2 * Real.pi) := by
  let r := Real.sqrt (t / (2 * Real.pi))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = t / (2*Real.pi) := Real.sq_sqrt (by positivity)
  have hv : t = (2*Real.pi)*r^2 := by rw [hr2]; field_simp
  have htail' (x : ℝ) (hx : r ≤ |x|) : 0 ≤ (radialGaussian p x).re := by
    rw [radialGaussian_apply, Complex.ofReal_re]
    refine mul_nonneg (htail _ ?_) (Real.exp_pos _).le
    rw [hv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_abs x, mul_self_le_mul_self hr hx]
  have hcont : Continuous (radialGaussian p) := by
    simp_rw [funext (radialGaussian_apply p)]
    have he := ((p.map (algebraMap ℚ ℝ)).continuous.comp
      (show Continuous (fun x : ℝ => 2*Real.pi*x^2) by fun_prop))
    simp only [Function.comp_def, Polynomial.eval_map] at he
    exact Complex.continuous_ofReal.comp (he.mul (by fun_prop))
  have hmem : t / (2*Real.pi) ∈ radiusProducts := by
    refine ⟨radialGaussian p, r, r, hr, hr, by rw [← hr2, sq],
      hcont, integrable_radialGaussian p, by rw [hself]; exact integrable_radialGaussian p, hnonzero,
      ?_, ?_, ?_, ?_, htail', by rw [hself]; exact htail'⟩
    · intro x
      simp [radialGaussian_apply]
    · intro x
      simp only [hself, radialGaussian_apply, Complex.ofReal_im, and_self]
    · simpa [radialGaussian_apply] using horigin
    · simpa [hself, radialGaussian_apply] using horigin
  apply csInf_le _ hmem
  refine ⟨0, ?_⟩
  rintro _ ⟨_, _, _, hr', hs', rfl, _⟩
  exact mul_nonneg hr' hs'

/-- Non-record regression control with an actual Fourier eigenfunction. -/
theorem control_upper : AplusSquared ≤ (sampleThreshold : ℝ) / (2*Real.pi) := by
  apply upper_from_polynomial samplePolynomial (sampleThreshold : ℝ)
  · norm_num [sampleThreshold]
  · exact fourier_quarticExample
  · intro h
    have hx := congrFun h 1
    change radialGaussian samplePolynomial 1 = (0 : ℂ) at hx
    rw [radialGaussian_apply, Complex.ofReal_eq_zero] at hx
    have hp := (mul_eq_zero.mp hx).resolve_right (Real.exp_pos _).ne'
    norm_num [samplePolynomial] at hp
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-3)]
  · norm_num [samplePolynomial]
  · intro z hz
    norm_num [sampleThreshold] at hz
    simp [samplePolynomial]
    nlinarith [mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ z-3 by linarith)]

theorem published_cutoff_lt_dual_threshold :
    2 * Real.pi * (30349081 / 100000000 : ℝ) < 191/100 := by
  linarith [Real.pi_lt_d4]

end NextProof
