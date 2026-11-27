import NextProof.TailKernel

namespace NextProof.Compact
open NextProof.Tail

/-- Positive integer divisor, used for outward rounding. -/
def quotient (d : ℤ) (w : List ℤ) := w.map (fun a => a/d)

theorem quotient_le (d : ℤ) (hd : 0 < d) (w : List ℤ) (x : ℝ) (hx : 0 ≤ x) :
    (d : ℝ)*horner x (quotient d w) ≤ horner x w := by
  induction w with
  | nil => simp [quotient,horner]
  | cons a as ih =>
    have h : d*(a/d) ≤ a := by
      have := Int.emod_nonneg a (ne_of_gt hd)
      linarith [Int.emod_add_mul_ediv a d]
    have h' : (d : ℝ)*(↑(a/d) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    simp only [quotient,List.map_cons,horner] at *
    nlinarith only [h', mul_le_mul_of_nonneg_left ih hx]

def absSum : List ℤ → ℤ
  | [] => 0
  | a::as => |a|+absSum as

theorem tail_bound (w : List ℤ) (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    |horner x w| ≤ (absSum w : ℝ) := by
  induction w with
  | nil => simp [horner,absSum]
  | cons a as ih =>
    simp only [horner, absSum, Int.cast_add, Int.cast_abs]
    have h : |x * horner x as| ≤ |horner x as| := by
      rw [abs_mul, abs_of_nonneg hx]
      simpa using mul_le_mul_of_nonneg_right hx' (abs_nonneg (horner x as))
    exact (abs_add_le ..).trans (add_le_add_right (h.trans ih) _)

theorem horner_append_real (w v : List ℤ) (x : ℝ) :
    horner x (w++v) = horner x w+x^w.length*horner x v := by
  induction w with
  | nil => simp [horner]
  | cons a as ih => simp only [List.cons_append,horner,ih,List.length_cons,pow_succ]; ring

/-- Discard a tail with its entire absolute mass charged to the constant term. -/
def truncate (n : ℕ) : List ℤ → List ℤ
  | [] => []
  | a::as => (a-absSum (as.drop n))::as.take n

theorem truncate_le (n : ℕ) (w : List ℤ) (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    horner x (truncate n w) ≤ horner x w := by
  cases w with
  | nil => rfl
  | cons a as =>
    have he := horner_append_real (as.take n) (as.drop n) x
    rw [List.take_append_drop] at he
    have hb := (abs_le.mp (tail_bound (as.drop n) x hx hx')).1
    have ha : 0 ≤ (absSum (as.drop n) : ℝ) :=
      (abs_nonneg _).trans (tail_bound (as.drop n) x hx hx')
    have hc := mul_nonneg (sub_nonneg.mpr (show x*x^(as.take n).length ≤ 1 by
      simpa only [mul_one] using mul_le_mul hx' (pow_le_one₀ hx hx') (pow_nonneg hx _) zero_le_one)) ha
    have hd := mul_le_mul_of_nonneg_left hb (mul_nonneg hx (pow_nonneg hx (as.take n).length))
    simp only [truncate,horner,Int.cast_sub]
    nlinarith only [he, hc, hd, congrArg (fun y : ℝ => x*y) he]

/-- An integral expression for 2^length * p((x+s)/2). -/
def halfForm {R : Type*} [CommRing R] (x s : R) : List ℤ → R
  | [] => 0
  | a::as => (a:R)*(2 : R)^(as.length+1)+(x+s)*halfForm x s as

theorem half_value (s x : ℝ) (w : List ℤ) :
    halfForm x s w = (2:ℝ)^w.length*horner ((x+s)/2) w := by
  induction w with
  | nil => simp [halfForm,horner]
  | cons a as ih => simp only [halfForm,horner,ih,List.length_cons,pow_succ]; ring

/-- A comparison of the next local polynomial suffices for an entire half interval. -/
theorem half_positive {v w : List ℤ} (s d : ℤ) (hd : 0 < d)
    (hcomp : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (d:ℝ)*horner x w ≤ halfForm x (s:ℝ) v)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ horner x w)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) : 0 ≤ horner ((x+s)/2) v := by
  have hh := (mul_nonneg (show 0 ≤ (d:ℝ) by exact_mod_cast hd.le) (h x hx hx')).trans (hcomp x hx hx')
  rw [half_value] at hh
  exact nonneg_of_mul_nonneg_right hh (by positivity)

end NextProof.Compact
