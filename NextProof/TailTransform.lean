import NextProof.FourierLaguerre
import Mathlib.Data.Nat.Choose.Central

namespace NextProof.Tail
open Polynomial

private theorem ode (n : ℕ) :
    X*(laguerreHalf n).derivative.derivative +
      (C (1/2 : ℚ)-X)*(laguerreHalf n).derivative + C (n : ℚ)*laguerreHalf n = 0 := by
  rw [laguerreHalf]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  linear_combination C ((-1 : ℚ)^n/(n.factorial : ℚ)) * monicLaguerreHalf_ode n

theorem coefficient_step (n j : ℕ) :
    ((j : ℚ)+1)*((j : ℚ)+1/2)*(laguerreHalf n).coeff (j+1) =
    ((j : ℚ)-n)*(laguerreHalf n).coeff j := by
  have h := congrArg (fun p : ℚ[X] => p.coeff j) (ode n)
  cases j with
  | zero =>
    simp only [sub_mul, coeff_add, coeff_X_mul_zero, coeff_sub, coeff_C_mul, coeff_derivative,
      coeff_zero, Nat.cast_zero, Nat.cast_one, mul_one] at h ⊢
    linarith
  | succ j =>
    simp only [sub_mul, coeff_add, coeff_X_mul, coeff_sub, coeff_C_mul, coeff_derivative,
      coeff_zero, Nat.cast_succ] at h ⊢
    linear_combination h

theorem mode_origin_step (n : ℕ) :
    ((n : ℚ)+1)*(laguerreHalf (n+1)).coeff 0 = ((n : ℚ)+1/2)*(laguerreHalf n).coeff 0 := by
  simp only [laguerreHalf, monicLaguerreHalf, coeff_C_mul, sub_mul, coeff_sub, coeff_X_mul_zero,
    zero_sub, sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  field_simp

theorem mode_origin (n : ℕ) :
    (laguerreHalf n).coeff 0 = (n.centralBinom : ℚ)/4^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mode_origin_step n
    rw [ih] at h
    have hc := congrArg (fun x : ℕ => (x : ℚ)) (Nat.succ_mul_centralBinom_succ n)
    push_cast at hc
    rw [eq_div_iff (by positivity), pow_succ]
    field_simp at h
    apply mul_left_cancel₀ (a := (n : ℚ)+1) (by positivity)
    linear_combination 2*h - hc

/-- Odd double factorial, the integer denominator in the diagonal coefficient change. -/
def oddFactor : ℕ → ℕ
  | 0 => 1
  | j+1 => (2*j+1)*oddFactor j

private theorem choose_step (n j : ℕ) : ((j : ℚ)+1)*n.choose (j+1) =
    ((n : ℚ)-j)*n.choose j := by
  have h := congrArg (fun x : ℕ => (x : ℚ)) (Nat.add_one_mul_choose_eq n j)
  rw [Nat.choose_succ_succ] at h
  push_cast at h
  linarith

theorem coefficient_transform (n j : ℕ) :
    (oddFactor j : ℚ)*(laguerreHalf n).coeff j =
      (-2 : ℚ)^j * ((n.centralBinom : ℚ)/4^n) * n.choose j := by
  induction j with
  | zero => simp [oddFactor,mode_origin]
  | succ j ih =>
    have h := coefficient_step n j
    have hc := choose_step n j
    rw [oddFactor, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, pow_succ]
    apply mul_left_cancel₀ (a := (j : ℚ)+1) (by positivity)
    linear_combination (2*(oddFactor j : ℚ))*h + 2*((j : ℚ)-n)*ih +
      (2*(-2 : ℚ)^j*((n.centralBinom : ℚ)/4^n))*hc

/-- The complete Laguerre-to-power transform is one shift by one followed by
a diagonal scaling. This is the coefficient identity used in projection/descartes.py. -/
theorem shifted_modes_coefficient {ι : Type*} (s : Finset ι) (w : ι → ℚ) (k : ι → ℕ) (j : ℕ) :
    (oddFactor j : ℚ) * (∑ i ∈ s, C (w i)*laguerreHalf (k i)).coeff j =
      (-2 : ℚ)^j * ((∑ i ∈ s, C (w i*((k i).centralBinom : ℚ)/4^(k i)) * X^(k i)).comp (1+X)).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, add_comp, mul_comp, C_comp, pow_comp, X_comp, coeff_add,
      coeff_C_mul, coeff_one_add_X_pow, mul_add]
    rw [ih]
    linear_combination (w i)*coefficient_transform (k i) j

end NextProof.Tail
