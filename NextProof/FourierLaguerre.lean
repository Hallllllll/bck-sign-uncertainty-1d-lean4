import NextProof.Fourier

/-! The dimension-one Laguerre modes in the radial coordinate `t = 2πx²`. -/

namespace NextProof

open Polynomial
open scoped FourierTransform

/-- Monic normalization of the generalized Laguerre polynomial with parameter -1/2. -/
noncomputable def monicLaguerreHalf : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => (X - C ((n : ℚ) + 1/2)) * monicLaguerreHalf n -
      X * (monicLaguerreHalf n).derivative

private theorem laguerre_diff_step (n : ℕ) (p : ℚ[X])
    (h : X * p.derivative.derivative + (C (1/2 : ℚ) - X) * p.derivative + C (n : ℚ) * p = 0) :
    ((X - C ((n : ℚ) + 1/2)) * p - X * p.derivative).derivative =
      C ((n : ℚ) + 1) * (p - p.derivative) := by
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, one_mul,
    map_add, map_one]
  linear_combination -h

theorem monicLaguerreHalf_ode (n : ℕ) :
    X * (monicLaguerreHalf n).derivative.derivative +
      (C (1/2 : ℚ) - X) * (monicLaguerreHalf n).derivative +
      C (n : ℚ) * monicLaguerreHalf n = 0 := by
  induction n with
  | zero => simp [monicLaguerreHalf]
  | succ n ih =>
    rw [monicLaguerreHalf, laguerre_diff_step n _ ih]
    simp only [derivative_mul, derivative_C, derivative_one, zero_mul, zero_add, derivative_sub,
      Nat.cast_succ, map_add, map_one]
    linear_combination -(C (n : ℚ) + 1) * ih

theorem monicLaguerreHalf_derivative_succ (n : ℕ) :
    (monicLaguerreHalf (n+1)).derivative =
      C ((n : ℚ) + 1) * (monicLaguerreHalf n - (monicLaguerreHalf n).derivative) :=
  laguerre_diff_step n _ (monicLaguerreHalf_ode n)

/-- Three-term recurrence for the monic normalization. -/
theorem monicLaguerreHalf_recurrence (n : ℕ) :
    monicLaguerreHalf (n+2) =
      (X - C (2 * (n : ℚ) + 5/2)) * monicLaguerreHalf (n+1) -
      C (((n : ℚ) + 1) * ((n : ℚ) + 1/2)) * monicLaguerreHalf n := by
  rw [monicLaguerreHalf, monicLaguerreHalf_derivative_succ, monicLaguerreHalf]
  rw [show (5/2 : ℚ) = 2 + 1/2 by norm_num]
  push_cast
  simp only [map_add, map_mul, C_ofNat, map_one]
  ring

private lemma raisingPolynomial_C_mul (c : ℂ) (p : ℂ[X]) :
    raisingPolynomial (C c * p) = C c * raisingPolynomial p := by
  simp only [raisingPolynomial, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

private lemma raising_radial (p : ℂ[X]) :
    raisingPolynomial (radialEmbed p) =
      C (4 * (Real.pi : ℂ)) * X * radialEmbed (p.derivative - p) := by
  rw [raisingPolynomial, derivative_radialEmbed]
  simp only [radialEmbed, sub_comp]
  ring

private lemma raising_X_radial (p : ℂ[X]) :
    raisingPolynomial (X * radialEmbed p) =
      radialEmbed (p + 2 * X * (p.derivative - p)) := by
  rw [raisingPolynomial, derivative_mul, derivative_X, one_mul, derivative_radialEmbed]
  simp only [radialEmbed, add_comp, mul_comp, sub_comp, ofNat_comp, X_comp]
  simp only [map_mul, C_ofNat]
  ring

private theorem twice_raising_monic (n : ℕ) :
    raisingPolynomial (raisingPolynomial (radialEmbed ((monicLaguerreHalf n).map (algebraMap ℚ ℂ)))) =
      C (8 * (Real.pi : ℂ)) * radialEmbed ((monicLaguerreHalf (n+1)).map (algebraMap ℚ ℂ)) := by
  have hp := monicLaguerreHalf_ode n
  have h : (monicLaguerreHalf n).derivative - monicLaguerreHalf n +
      2 * X * (((monicLaguerreHalf n).derivative - monicLaguerreHalf n).derivative -
        ((monicLaguerreHalf n).derivative - monicLaguerreHalf n)) =
      2 * monicLaguerreHalf (n+1) := by
    rw [monicLaguerreHalf, derivative_sub, map_add]
    have hh : 2 * C (1/2 : ℚ) = 1 := by
      rw [← C_ofNat, ← C_mul]
      norm_num
    linear_combination 2 * hp + ((monicLaguerreHalf n) - (monicLaguerreHalf n).derivative) * hh
  rw [raising_radial, mul_assoc, raisingPolynomial_C_mul, raising_X_radial]
  have hc := congrArg (fun p : ℚ[X] => p.map (algebraMap ℚ ℂ)) h
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_ofNat,
    map_X, derivative_sub, derivative_map] at hc ⊢
  rw [hc]
  simp only [radialEmbed, mul_comp, ofNat_comp]
  simp only [map_mul, C_ofNat]
  ring

private theorem raisedPolynomial_eq_monic (n : ℕ) :
    raisedPolynomial (2*n) = C ((8 * (Real.pi : ℂ)) ^ n) *
      radialEmbed ((monicLaguerreHalf n).map (algebraMap ℚ ℂ)) := by
  induction n with
  | zero => simp [monicLaguerreHalf, raisedPolynomial, radialEmbed]
  | succ n ih =>
    rw [Nat.mul_succ, raisedPolynomial, raisedPolynomial, ih,
      raisingPolynomial_C_mul, raisingPolynomial_C_mul, twice_raising_monic, pow_succ]
    simp only [map_mul, mul_assoc]

theorem fourier_monicLaguerreHalf (n : ℕ) :
    𝓕 (radialGaussian (monicLaguerreHalf n)) =
      fun x => (-1 : ℂ)^n * radialGaussian (monicLaguerreHalf n) x := by
  have hfun : polyGaussian (raisedPolynomial (2*n)) =
      fun x => (8 * (Real.pi : ℂ))^n * radialGaussian (monicLaguerreHalf n) x := by
    funext x
    rw [raisedPolynomial_eq_monic]
    simp [polyGaussian, radialGaussian, mul_assoc]
  have h := fourier_raisedPolynomial (2*n)
  rw [hfun, fourier_const_mul, pow_mul, show (-Complex.I)^2 = -1 by
    rw [neg_sq, Complex.I_sq]] at h
  funext x
  have hx := congrFun h x
  dsimp only at hx
  have hc : (8 * (Real.pi : ℂ)) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  apply mul_left_cancel₀ hc
  rw [hx]
  ring

/-- Standard generalized Laguerre normalization, L₀=1, L₁=1/2-X. -/
noncomputable def laguerreHalf (n : ℕ) : ℚ[X] :=
  C ((-1 : ℚ)^n / (n.factorial : ℚ)) * monicLaguerreHalf n

@[simp] theorem laguerreHalf_zero : laguerreHalf 0 = 1 := by
  simp [laguerreHalf, monicLaguerreHalf]

@[simp] theorem laguerreHalf_one : laguerreHalf 1 = C (1/2 : ℚ) - X := by
  simp [laguerreHalf, monicLaguerreHalf]

private theorem laguerre_scale_succ (n : ℕ) :
    ((n : ℚ) + 1) * ((-1 : ℚ)^(n+1) / ((n+1).factorial : ℚ)) =
      -((-1 : ℚ)^n / (n.factorial : ℚ)) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  field_simp

/-- Standard three-term recurrence, with rational coefficients and no division of polynomials. -/
theorem laguerreHalf_recurrence (n : ℕ) :
    C ((n : ℚ) + 2) * laguerreHalf (n+2) =
      (C (2*(n : ℚ) + 5/2) - X) * laguerreHalf (n+1) -
      C ((n : ℚ) + 1/2) * laguerreHalf n := by
  let s (j : ℕ) : ℚ := (-1 : ℚ)^j / (j.factorial : ℚ)
  change C ((n : ℚ) + 2) * (C (s (n+2)) * _) = _ * (C (s (n+1)) * _) - _ * (C (s n) * _)
  have h₂ : ((n : ℚ) + 2) * s (n+2) = -s (n+1) := by
    convert! laguerre_scale_succ (n+1) using 2
    push_cast
    ring
  have h₁ : C ((n : ℚ)+1) * C (s (n+1)) = -C (s n) := by
    rw [← map_mul, laguerre_scale_succ, map_neg]
  rw [← mul_assoc, ← map_mul, h₂, map_neg, monicLaguerreHalf_recurrence, map_mul]
  linear_combination C ((n : ℚ)+1/2) * monicLaguerreHalf n * h₁

lemma radialGaussian_C_mul (a : ℚ) (p : ℚ[X]) :
    radialGaussian (C a * p) = fun x => (a : ℂ) * radialGaussian p x := by
  funext x
  simp [radialGaussian, radialEmbed, polyGaussian, mul_assoc]

lemma radialGaussian_add (p q : ℚ[X]) :
    radialGaussian (p + q) = fun x => radialGaussian p x + radialGaussian q x := by
  funext x
  simp [radialGaussian, radialEmbed, polyGaussian, add_mul]

theorem fourier_laguerreHalf (n : ℕ) :
    𝓕 (radialGaussian (laguerreHalf n)) =
      fun x => (-1 : ℂ)^n * radialGaussian (laguerreHalf n) x := by
  rw [laguerreHalf, radialGaussian_C_mul, fourier_const_mul, fourier_monicLaguerreHalf]
  funext x
  ring

/-- Every finite rational combination of even Laguerre modes is self-Fourier. -/
theorem fourier_evenLaguerre_sum {ι : Type*} (s : Finset ι) (a : ι → ℚ) (k : ι → ℕ) :
    𝓕 (radialGaussian (∑ i ∈ s, C (a i) * laguerreHalf (2*k i))) =
      radialGaussian (∑ i ∈ s, C (a i) * laguerreHalf (2*k i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [fourier_radialGaussian]
    simp [radialTransform]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, radialGaussian_add,
      fourier_add (integrable_radialGaussian _) (integrable_radialGaussian _), ih,
      radialGaussian_C_mul, fourier_const_mul, fourier_laguerreHalf, pow_mul]
    simp

end NextProof

#print axioms NextProof.fourier_radialGaussian
#print axioms NextProof.fourier_evenLaguerre_sum
#print axioms NextProof.laguerreHalf_recurrence
