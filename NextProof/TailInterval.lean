import NextProof.TailKernel

namespace NextProof.Tail
open Polynomial

/-- For a nonnegative argument x in [a/q,b/q], bound Horner from below.
Both entries are integers. The second entry is the common positive denominator. -/
def lower (a b q : ℤ) : List ℤ → ℤ × ℤ
  | [] => (0,1)
  | w::ws =>
    let (v,d) := lower a b q ws
    let d' := q*d
    (w*d'+(if 0 ≤ v then a else b)*v, d')

theorem lower_spec (ws : List ℤ) (a b q : ℤ) (x : ℝ)
    (hq : 0 < q) (hx : 0 ≤ x) (ha : (a : ℝ) ≤ q*x) (hb : q*x ≤ (b : ℝ)) :
    0 < (lower a b q ws).2 ∧
    ((lower a b q ws).1 : ℝ) ≤ ((lower a b q ws).2 : ℝ)*horner x ws := by
  induction ws with
  | nil => simp [lower, horner]
  | cons w ws ih =>
    obtain ⟨dpos, ih⟩ := ih
    have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq.le
    have h := mul_le_mul_of_nonneg_left ih (mul_nonneg hq' hx)
    constructor
    · exact mul_pos hq dpos
    · simp only [lower, horner, Int.cast_add, Int.cast_mul]
      split_ifs with hv
      · have hv' : 0 ≤ ((lower a b q ws).1 : ℝ) := by exact_mod_cast hv
        linarith only [mul_le_mul_of_nonneg_right ha hv', h]
      · have hv' : ((lower a b q ws).1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hv)
        linarith only [mul_le_mul_of_nonpos_right hb hv', h]

theorem interval_pos {p t : List ℤ} {c a b q : ℤ}
    (hid : horner (C c+X) p = horner (X : ℤ[X]) t)
    (hq : 0 < q) (ha : 0 ≤ a) (hgood : 0 < (lower a b q t).1)
    (x : ℝ) (hl : (a : ℝ) ≤ q*(x-c)) (hr : q*(x-c) ≤ (b : ℝ)) : 0 < horner x p := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : 0 ≤ x-c := nonneg_of_mul_nonneg_right ((by exact_mod_cast ha : (0 : ℝ) ≤ a).trans hl) hq'
  have h := lower_spec t a b q (x-c) hq hx hl hr
  rw [shift_eval hid]
  exact pos_of_mul_pos_right ((by exact_mod_cast hgood : (0 : ℝ) < _).trans_le h.2)
    (by exact_mod_cast h.1.le)

theorem ray_pos {p : List ℤ} {u : ℤ} {t : List ℤ} {c : ℤ}
    (hid : horner (C c+X) p = horner (X : ℤ[X]) (u::t))
    (hu : 0 < u) (ht : t.all (fun a => decide (0 ≤ a)) = true)
    (x : ℝ) (hx : (c : ℝ) ≤ x) : 0 < horner x p := by
  rw [shift_eval hid, horner]
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast hu)
    (mul_nonneg (sub_nonneg.mpr hx) (horner_nonneg _ ht (sub_nonneg.mpr hx)))

end NextProof.Tail
