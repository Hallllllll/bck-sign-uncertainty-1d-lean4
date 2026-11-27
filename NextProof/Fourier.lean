/-
Port of the FourierPolynomial and RadialFourier proofs in the Station sign-uncertainty
S1 formalization (Lean 4.25.2), adapted for the present mathlib. Source and
normalization are documented in FOURIER.md.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Ring

namespace NextProof

open MeasureTheory Polynomial
open scoped FourierTransform

noncomputable def gaussian (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (x : ℂ) ^ 2)

noncomputable def polyGaussian (p : ℂ[X]) (x : ℝ) : ℂ :=
  p.eval (x : ℂ) * gaussian x

lemma fourier_gaussian : 𝓕 gaussian = gaussian := by
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)
  unfold gaussian
  simpa using h

lemma integrable_monomial_gaussian (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * gaussian x) := by
  have hr : Integrable (fun x : ℝ => x ^ n * Real.exp (-Real.pi * x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := (n : ℝ)) (by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith))
  have hc := hr.ofReal (𝕜 := ℂ)
  convert! hc using 1 with x
  simp [gaussian, Complex.ofReal_exp]

lemma integrable_polyGaussian (p : ℂ[X]) : Integrable (polyGaussian p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert! hp.add hq using 1
      funext x
      simp [polyGaussian, add_mul]
  | monomial n a =>
      convert! (integrable_monomial_gaussian n).const_mul a using 1
      funext x
      simp [polyGaussian, mul_assoc]

noncomputable def raisingPolynomial (p : ℂ[X]) : ℂ[X] :=
  p.derivative - C (4 * (Real.pi : ℂ)) * X * p

noncomputable def raisingOperator (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x - (2 * Real.pi * x) • f x

lemma hasDerivAt_polyGaussian (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (polyGaussian p) (polyGaussian
      (p.derivative - C (2 * (Real.pi : ℂ)) * X * p) x) x := by
  have hp := (p.hasDerivAt (x : ℂ))
  have hg := ((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(Real.pi : ℂ))).cexp
  convert! (hp.mul hg).comp_ofReal using 1
  simp [polyGaussian, gaussian, pow_two]
  ring_nf

lemma deriv_polyGaussian (p : ℂ[X]) :
    deriv (polyGaussian p) =
      polyGaussian (p.derivative - C (2 * (Real.pi : ℂ)) * X * p) := by
  funext x
  exact (hasDerivAt_polyGaussian p x).deriv

lemma raising_polyGaussian (p : ℂ[X]) :
    raisingOperator (polyGaussian p) = polyGaussian (raisingPolynomial p) := by
  funext x
  rw [raisingOperator, deriv_polyGaussian]
  simp only [polyGaussian, raisingPolynomial, eval_sub, eval_mul, eval_C, eval_X,
    Complex.real_smul]
  push_cast
  ring

lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (fun x => c * f x) = fun x => c * 𝓕 f x := by
  exact VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) f c

lemma fourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (fun x => f x + g x) = fun x => 𝓕 f x + 𝓕 g x := by
  exact VectorFourier.fourierIntegral_add (L := innerₗ ℝ) Real.continuous_fourierChar
    (by fun_prop) hf hg

lemma fourier_mul_x (p : ℂ[X]) :
    𝓕 (fun x : ℝ => (x : ℂ) * polyGaussian p x) =
      fun x => Complex.I / (2 * Real.pi) * deriv (𝓕 (polyGaussian p)) x := by
  have hd := Real.deriv_fourier (integrable_polyGaussian p) (by
    convert! integrable_polyGaussian (X * p) using 1
    funext x
    simp [polyGaussian, Complex.real_smul, mul_assoc])
  have hs := fourier_const_mul (-2 * Real.pi * Complex.I)
    (fun x : ℝ => (x : ℂ) * polyGaussian p x)
  rw [hd]
  have hfun : (fun x : ℝ => (-2 * Real.pi * Complex.I * x) • polyGaussian p x) =
      fun x : ℝ => (-2 * Real.pi * Complex.I) * ((x : ℂ) * polyGaussian p x) := by
    funext x
    simp only [smul_eq_mul]
    ring
  rw [hfun, hs]
  funext x
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

theorem fourier_raising_polyGaussian (p : ℂ[X]) :
    𝓕 (raisingOperator (polyGaussian p)) =
      fun x => -Complex.I * raisingOperator (𝓕 (polyGaussian p)) x := by
  have hdiff : Integrable (deriv (polyGaussian p)) := by
    rw [deriv_polyGaussian]
    exact integrable_polyGaussian _
  have hmul : Integrable (fun x : ℝ => (x : ℂ) * polyGaussian p x) := by
    convert! integrable_polyGaussian (X * p) using 1
    funext x
    simp [polyGaussian, mul_assoc]
  have hscaled : Integrable
      (fun x : ℝ => (-2 * Real.pi : ℂ) * ((x : ℂ) * polyGaussian p x)) :=
    hmul.const_mul _
  have hshape : raisingOperator (polyGaussian p) = fun x =>
      deriv (polyGaussian p) x + (-2 * Real.pi : ℂ) * ((x : ℂ) * polyGaussian p x) := by
    funext x
    simp only [raisingOperator, Complex.real_smul]
    push_cast
    ring
  rw [hshape, fourier_add hdiff hscaled, fourier_const_mul,
    Real.fourier_deriv (integrable_polyGaussian p)
      (fun x => (hasDerivAt_polyGaussian p x).differentiableAt)
      hdiff,
    fourier_mul_x]
  funext x
  simp only [smul_eq_mul, raisingOperator,
    Complex.real_smul]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

noncomputable def raisedPolynomial : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => raisingPolynomial (raisedPolynomial n)

lemma raisingOperator_const_mul (c : ℂ) (p : ℂ[X]) :
    raisingOperator (fun x => c * polyGaussian p x) =
      fun x => c * raisingOperator (polyGaussian p) x := by
  funext x
  have hd := (hasDerivAt_polyGaussian p x).const_mul c
  simp only [raisingOperator, hd.deriv, Complex.real_smul]
  rw [← congrFun (deriv_polyGaussian p) x]
  push_cast
  ring

theorem fourier_raisedPolynomial (m : ℕ) :
    𝓕 (polyGaussian (raisedPolynomial m)) =
      fun x => (-Complex.I) ^ m * polyGaussian (raisedPolynomial m) x := by
  induction m with
  | zero =>
      have hpg : polyGaussian 1 = gaussian := by
        funext x
        simp [polyGaussian]
      simpa [raisedPolynomial, hpg] using fourier_gaussian
  | succ m ih =>
      rw [raisedPolynomial, ← raising_polyGaussian, fourier_raising_polyGaussian, ih,
        raisingOperator_const_mul]
      funext x
      simp only [pow_succ]
      ring

theorem fourier_raisedPolynomial_four_mul (j : ℕ) :
    𝓕 (polyGaussian (raisedPolynomial (4 * j))) =
      polyGaussian (raisedPolynomial (4 * j)) := by
  rw [fourier_raisedPolynomial]
  funext x
  rw [show (-Complex.I) ^ (4 * j) = 1 by
    rw [pow_mul, show (-Complex.I) ^ 4 = 1 by
      calc
        (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
        _ = 1 := by rw [Complex.I_sq]; norm_num,
      one_pow],
    one_mul]

noncomputable def spatialDerivativePolynomial (p : ℂ[X]) : ℂ[X] :=
  p.derivative - C (2 * (Real.pi : ℂ)) * X * p

noncomputable def radialEmbed (p : ℂ[X]) : ℂ[X] :=
  p.comp (C (2 * (Real.pi : ℂ)) * X ^ 2)

noncomputable def radialOperator {R : Type*} [CommRing R] (p : R[X]) : R[X] :=
  (1 - X) * p + (4 * X - 2) * p.derivative - 4 * X * p.derivative.derivative

noncomputable def radialBasis {R : Type*} [CommRing R] : ℕ → R[X]
  | 0 => 1
  | n + 1 => radialOperator (radialBasis n)

noncomputable def radialTransform {R : Type*} [CommRing R] (p : R[X]) : R[X] :=
  p.sum fun n c => C c * radialBasis n

lemma deriv_const_mul_polyGaussian (c : ℂ) (p : ℂ[X]) :
    deriv (fun x : ℝ => c * polyGaussian p x) =
      fun x => c * polyGaussian (spatialDerivativePolynomial p) x := by
  funext x
  have h := (hasDerivAt_polyGaussian p x).const_mul c
  simpa [spatialDerivativePolynomial] using h.deriv

lemma fourier_X_mul_polyGaussian (p : ℂ[X]) :
    𝓕 (polyGaussian (X * p)) =
      fun x => Complex.I / (2 * Real.pi) * deriv (𝓕 (polyGaussian p)) x := by
  have hfun : polyGaussian (X * p) =
      fun x : ℝ => (x : ℂ) * polyGaussian p x := by
    funext x
    simp [polyGaussian]
    ring
  rw [hfun]
  exact fourier_mul_x p

lemma radialEmbed_X_mul (p : ℂ[X]) :
    radialEmbed (X * p) = C (2 * (Real.pi : ℂ)) * X ^ 2 * radialEmbed p := by
  simp only [radialEmbed, mul_comp, X_comp, C_mul, pow_two]

lemma derivative_radialEmbed (p : ℂ[X]) :
    (radialEmbed p).derivative =
      C (4 * (Real.pi : ℂ)) * X * radialEmbed p.derivative := by
  simp only [radialEmbed, derivative_comp, derivative_mul, derivative_C, derivative_pow,
    derivative_X, zero_mul, zero_add]
  have hc : C (4 * (Real.pi : ℂ)) = C (2 * (Real.pi : ℂ)) * C 2 := by
    rw [← C_mul]
    congr 1
    ring
  rw [hc]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, C_ofNat]
  ring

lemma spatialDerivative_radial (p : ℂ[X]) :
    spatialDerivativePolynomial (radialEmbed p) =
      C (2 * (Real.pi : ℂ)) * X * radialEmbed (2 * p.derivative - p) := by
  rw [spatialDerivativePolynomial, derivative_radialEmbed]
  simp only [radialEmbed, sub_comp, mul_comp, ofNat_comp]
  have hc : C (4 * (Real.pi : ℂ)) = C (2 * (Real.pi : ℂ)) * C 2 := by
    rw [← C_mul]
    congr 1
    ring
  rw [hc]
  simp only [Nat.cast_ofNat, C_ofNat]
  ring

lemma spatialDerivative_radial_aux (p : ℂ[X]) :
    spatialDerivativePolynomial
        (C (2 * (Real.pi : ℂ)) * X * radialEmbed p) =
      C (2 * (Real.pi : ℂ)) *
        radialEmbed (p + 2 * X * p.derivative - X * p) := by
  rw [spatialDerivativePolynomial]
  simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add]
  rw [derivative_radialEmbed]
  simp only [radialEmbed, add_comp, sub_comp, mul_comp, ofNat_comp, X_comp]
  have hc : C (4 * (Real.pi : ℂ)) = C (2 * (Real.pi : ℂ)) * C 2 := by
    rw [← C_mul]
    congr 1
    ring
  rw [hc]
  simp only [Nat.cast_ofNat, mul_one, C_ofNat]
  ring

lemma radialOperator_identity (p : ℂ[X]) :
    C (-(1 / (2 * (Real.pi : ℂ)))) *
        spatialDerivativePolynomial (spatialDerivativePolynomial (radialEmbed p)) =
      radialEmbed (radialOperator p) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [spatialDerivative_radial, spatialDerivative_radial_aux]
  have hcancel : C (-(1 / (2 * (Real.pi : ℂ)))) * C (2 * (Real.pi : ℂ)) = -1 := by
    rw [← C_mul]
    have hs : -(1 / (2 * (Real.pi : ℂ))) * (2 * Real.pi) = -1 := by
      field_simp [hpi]
    rw [hs]
    simp
  rw [← mul_assoc, hcancel, neg_one_mul]
  simp only [radialEmbed]
  rw [← neg_comp]
  apply congrArg (fun q : ℂ[X] => q.comp (C (2 * (Real.pi : ℂ)) * X ^ 2))
  simp only [radialOperator, derivative_sub, derivative_mul, derivative_ofNat,
    zero_mul, zero_add]
  ring

theorem fourier_radial_mul {p q : ℂ[X]}
    (h : 𝓕 (polyGaussian (radialEmbed p)) = polyGaussian (radialEmbed q)) :
    𝓕 (polyGaussian (radialEmbed (X * p))) =
      polyGaussian (radialEmbed (radialOperator q)) := by
  have hX :
      𝓕 (polyGaussian (X * radialEmbed p)) =
        fun x => Complex.I / (2 * Real.pi) *
          polyGaussian (spatialDerivativePolynomial (radialEmbed q)) x := by
    rw [fourier_X_mul_polyGaussian, h, deriv_polyGaussian]
    rfl
  have hXX :
      𝓕 (polyGaussian (X * (X * radialEmbed p))) =
        fun x => (Complex.I / (2 * Real.pi)) ^ 2 *
          polyGaussian
            (spatialDerivativePolynomial (spatialDerivativePolynomial (radialEmbed q))) x := by
    rw [fourier_X_mul_polyGaussian, hX, deriv_const_mul_polyGaussian]
    funext x
    ring
  rw [radialEmbed_X_mul]
  have hsource :
      polyGaussian (C (2 * (Real.pi : ℂ)) * X ^ 2 * radialEmbed p) =
        fun x => (2 * (Real.pi : ℂ)) *
          polyGaussian (X * (X * radialEmbed p)) x := by
    funext x
    simp only [polyGaussian, eval_mul, eval_C, eval_pow, eval_X]
    ring
  rw [hsource, fourier_const_mul, hXX]
  funext x
  rw [← radialOperator_identity q]
  simp only [polyGaussian, eval_mul, eval_C]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

theorem fourier_radialBasis (n : ℕ) :
    𝓕 (polyGaussian (radialEmbed (X ^ n))) =
      polyGaussian (radialEmbed (radialBasis n : ℂ[X])) := by
  induction n with
  | zero =>
      have hembed : radialEmbed (1 : ℂ[X]) = 1 := by simp [radialEmbed]
      simp only [radialBasis]
      rw [pow_zero, hembed]
      have hpg : polyGaussian 1 = gaussian := by
        funext x
        simp [polyGaussian]
      rw [hpg]
      exact fourier_gaussian
  | succ n ih =>
      simpa [pow_succ, radialBasis, mul_comm] using fourier_radial_mul ih

lemma radialTransform_add {R : Type*} [CommRing R] (p q : R[X]) :
    radialTransform (p + q) = radialTransform p + radialTransform q := by
  apply sum_add_index
  · intro n
    simp
  · intro n a b
    simp only [C_add]
    ring

lemma radialTransform_monomial {R : Type*} [CommRing R] (n : ℕ) (c : R) :
    radialTransform (monomial n c) = C c * radialBasis n := by
  simp [radialTransform]

lemma radialBasis_map (n : ℕ) :
    (radialBasis n : ℚ[X]).map (algebraMap ℚ ℂ) = (radialBasis n : ℂ[X]) := by
  induction n with
  | zero => simp [radialBasis]
  | succ n ih =>
      simp only [radialBasis]
      simp [radialOperator, ih, ← derivative_map]

lemma radialTransform_map (p : ℚ[X]) :
    (radialTransform p).map (algebraMap ℚ ℂ) =
      radialTransform (p.map (algebraMap ℚ ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        (radialTransform (p + q)).map (algebraMap ℚ ℂ) =
            (radialTransform p + radialTransform q).map (algebraMap ℚ ℂ) := by
              rw [radialTransform_add]
        _ = (radialTransform p).map (algebraMap ℚ ℂ) +
            (radialTransform q).map (algebraMap ℚ ℂ) := by rw [Polynomial.map_add]
        _ = radialTransform (p.map (algebraMap ℚ ℂ)) +
            radialTransform (q.map (algebraMap ℚ ℂ)) := by rw [hp, hq]
        _ = radialTransform (p.map (algebraMap ℚ ℂ) +
            q.map (algebraMap ℚ ℂ)) := (radialTransform_add _ _).symm
        _ = radialTransform ((p + q).map (algebraMap ℚ ℂ)) := by
          rw [Polynomial.map_add]
  | monomial n c => simp [radialTransform_monomial, radialBasis_map]

theorem fourier_radialTransform (p : ℂ[X]) :
    𝓕 (polyGaussian (radialEmbed p)) =
      polyGaussian (radialEmbed (radialTransform p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hsource : polyGaussian (radialEmbed (p + q)) =
          fun x => polyGaussian (radialEmbed p) x + polyGaussian (radialEmbed q) x := by
        funext x
        simp [polyGaussian, radialEmbed, add_mul]
      rw [hsource, fourier_add (integrable_polyGaussian _) (integrable_polyGaussian _), hp, hq,
        radialTransform_add]
      funext x
      simp [polyGaussian, radialEmbed, add_mul]
  | monomial n c =>
      have hsource : polyGaussian (radialEmbed (monomial n c)) =
          fun x => c * polyGaussian (radialEmbed (X ^ n)) x := by
        funext x
        simp [polyGaussian, radialEmbed, mul_assoc]
      rw [hsource, fourier_const_mul, fourier_radialBasis, radialTransform_monomial]
      funext x
      simp [polyGaussian, radialEmbed, mul_assoc]


/-- The rational polynomial evaluated at the dimension-one radial coordinate, times the Gaussian. -/
noncomputable def radialGaussian (p : ℚ[X]) : ℝ → ℂ :=
  polyGaussian (radialEmbed (p.map (algebraMap ℚ ℂ)))

theorem integrable_radialGaussian (p : ℚ[X]) : Integrable (radialGaussian p) :=
  integrable_polyGaussian _

theorem fourier_radialGaussian (p : ℚ[X]) :
    𝓕 (radialGaussian p) = radialGaussian (radialTransform p) := by
  unfold radialGaussian
  rw [radialTransform_map, fourier_radialTransform]

/-- Real-valued form for comparison with sign and tail certificates. -/
theorem radialGaussian_apply (p : ℚ[X]) (x : ℝ) :
    radialGaussian p x = ((p.eval₂ (algebraMap ℚ ℝ) (2 * Real.pi * x ^ 2) *
      Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) := by
  have hcast (t : ℝ) : ((p.eval₂ (algebraMap ℚ ℝ) t : ℝ) : ℂ) =
      p.eval₂ (algebraMap ℚ ℂ) (t : ℂ) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n c => simp [eval₂_monomial]
  simp [radialGaussian, polyGaussian, radialEmbed, gaussian, eval_map, eval_comp,
    Complex.ofReal_exp, hcast]

/-- A nonconstant self-Fourier example with zero at the origin. -/
theorem fourier_quarticExample :
    𝓕 (radialGaussian (X ^ 2 - 3 * X)) = radialGaussian (X ^ 2 - 3 * X) := by
  rw [fourier_radialGaussian]
  apply congrArg radialGaussian
  have h : (X ^ 2 - 3 * X : ℚ[X]) = monomial 2 1 + monomial 1 (-3) := by
    simp [← C_mul_X_pow_eq_monomial, C_ofNat]
    ring
  conv_lhs => rw [h, radialTransform_add, radialTransform_monomial, radialTransform_monomial]
  norm_num [radialBasis, radialOperator, derivative_sub, derivative_mul, C_ofNat]
  ring

end NextProof
