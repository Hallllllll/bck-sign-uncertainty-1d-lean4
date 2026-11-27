import NextProof.FourierLaguerre
import Mathlib.Algebra.Polynomial.Inductions

namespace NextProof.Tail
open Polynomial

/-- Any integer polynomial whose coefficients fit strictly between -B and B
is determined to be zero by one zero evaluation at B. -/
theorem packed_zero {p : ℤ[X]} {B : ℤ} (hB : 0 < B)
    (hsmall : ∀ i, |p.coeff i| < B) (hval : p.eval B = 0) : p = 0 := by
  ext i
  simp only [coeff_zero]
  induction i generalizing p with
  | zero =>
    have h := congrArg (eval B) (divX_mul_X_add p)
    simp only [eval_add, eval_mul, eval_X, eval_C, hval] at h
    exact Int.eq_zero_of_abs_lt_dvd ⟨-(p.divX.eval B), by linarith⟩ (hsmall 0)
  | succ i ih =>
    have h := congrArg (eval B) (divX_mul_X_add p)
    simp only [eval_add, eval_mul, eval_X, eval_C, hval] at h
    have hz := Int.eq_zero_of_abs_lt_dvd (m := B) (x := p.coeff 0)
      ⟨-(p.divX.eval B), by linarith⟩ (hsmall 0)
    rw [hz, add_zero] at h
    rw [← coeff_divX]
    exact ih (fun j => by simpa only [coeff_divX] using hsmall (j+1))
      ((mul_eq_zero.mp h).resolve_right hB.ne')

def Bounded (p : ℤ[X]) (m : ℤ) := ∀ i, |p.coeff i| ≤ m

theorem packed_eq {p q : ℤ[X]} {B m n : ℤ} (hp : Bounded p m) (hq : Bounded q n)
    (hB : 0 < B) (h : m+n < B) (hv : p.eval B = q.eval B) : p=q := by
  apply sub_eq_zero.mp
  apply packed_zero hB
  · intro i
    rw [coeff_sub]
    exact lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add (hp i) (hq i))) h
  · simp [hv]

theorem bound_add {p q : ℤ[X]} {a b : ℤ} (hp : Bounded p a) (hq : Bounded q b) :
    Bounded (p+q) (a+b) := fun i => by
  rw [coeff_add]
  exact (abs_add_le ..).trans (add_le_add (hp i) (hq i))

theorem bound_const (a : ℤ) : Bounded (C a) |a| := fun i => by
  cases i <;> simp only [coeff_C_zero, coeff_C_succ, abs_zero, le_refl, abs_nonneg]

theorem bound_smul (k : ℤ) {p : ℤ[X]} {m : ℤ} (hp : Bounded p m) :
    Bounded (C k * p) (|k| * m) := fun i => by
  rw [coeff_C_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hp i) (abs_nonneg _)

theorem bound_X {p : ℤ[X]} {m : ℤ} (hp : Bounded p m) : Bounded (X*p) m := fun i => by
  cases i with
  | zero => simpa using (abs_nonneg _).trans (hp 0)
  | succ i => simpa using hp i

/-- Low-to-high coefficient Horner evaluation. -/
def horner {R : Type*} [Ring R] (x : R) : List ℤ → R
  | [] => 0
  | a::l => a + x * horner x l

theorem horner_eval (p : ℤ[X]) (l : List ℤ) (x : ℤ) :
    (horner p l).eval x = horner (p.eval x) l := by
  induction l with
  | nil => simp [horner]
  | cons a l ih => simp [horner, ih]

def major (k : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::l => |a| + k * major k l

theorem horner_bound (c : ℤ) (l : List ℤ) :
    Bounded (horner (C c + X) l) (major (|c|+1) l) := by
  induction l with
  | nil => intro i; simp [horner, major]
  | cons a l ih =>
    simp only [horner, major, add_mul, one_mul]
    apply bound_add
    · simpa using bound_const a
    · exact bound_add (bound_smul c ih) (bound_X ih)

theorem shift_eq {a b : List ℤ} {c B : ℤ} (hB : 0 < B)
    (hsize : major (|c|+1) a + major 1 b < B)
    (hval : horner (c+B) a = horner B b) :
    horner (C c+X) a = horner (X : ℤ[X]) b := by
  apply packed_eq (horner_bound c a) (by simpa using horner_bound 0 b) hB hsize
  simpa only [horner_eval, eval_add, eval_C, eval_X] using hval

theorem horner_real (p : ℤ[X]) (l : List ℤ) (x : ℝ) :
    (horner p l).eval₂ (Int.castRingHom ℝ) x =
      horner (p.eval₂ (Int.castRingHom ℝ) x) l := by
  induction l with
  | nil => simp [horner]
  | cons a l ih =>
    have ha : (a : ℤ[X]).eval₂ (Int.castRingHom ℝ) x = (a : ℝ) := by
      rw [← C_eq_intCast, eval₂_C]; rfl
    simp only [horner, eval₂_add, eval₂_mul, ih, ha]

theorem shift_eval {a b : List ℤ} {c : ℤ}
    (h : horner (C c+X) a = horner (X : ℤ[X]) b) (x : ℝ) :
    horner x a = horner (x-c) b := by
  have e := congrArg (fun p : ℤ[X] => p.eval₂ (Int.castRingHom ℝ) (x-c)) h
  simp only [horner_real, eval₂_add, eval₂_C, eval₂_X] at e
  change horner ((c : ℝ) + (x-c)) a = _ at e
  rwa [show (c : ℝ) + (x-c) = x by ring] at e

/-- On [0,1], discard positive higher-order contributions for a rigorous lower bound. -/
def unitLower : List ℤ → ℤ
  | [] => 0
  | a::l => a + min 0 (unitLower l)

theorem unitLower_le (l : List ℤ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (unitLower l : ℝ) ≤ horner x l := by
  induction l with
  | nil => simp [horner, unitLower]
  | cons a l ih =>
    simp only [unitLower, horner, Int.cast_add, Int.cast_min, Int.cast_zero, add_le_add_iff_left]
    rcases le_total (unitLower l : ℝ) 0 with h | h
    · rw [min_eq_right h]
      nlinarith [mul_le_mul_of_nonneg_left ih hx, mul_nonneg (sub_nonneg.mpr hx') (neg_nonneg.mpr h)]
    · rw [min_eq_left h]
      exact mul_nonneg hx (h.trans ih)

theorem horner_nonneg (l : List ℤ) (h : l.all (fun a => decide (0 ≤ a)) = true)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ horner x l := by
  induction l with
  | nil => simp [horner]
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact add_nonneg (by exact_mod_cast h.1) (mul_nonneg hx (ih h.2))

end NextProof.Tail
