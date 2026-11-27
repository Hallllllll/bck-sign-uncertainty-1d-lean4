import NextProof.FourierLaguerre

namespace NextProof.Exterior

open Polynomial
open scoped FourierTransform

noncomputable def mode (n : ℕ) (x : ℝ) : ℝ :=
  (laguerreHalf n).eval₂ (algebraMap ℚ ℝ) x

noncomputable def monic (n : ℕ) (x : ℝ) : ℝ :=
  (monicLaguerreHalf n).eval₂ (algebraMap ℚ ℝ) x

private theorem monic_succ_succ (n : ℕ) (x : ℝ) :
    monic (n+2) x = (x - (2*(n : ℝ)+5/2))*monic (n+1) x -
      ((n : ℝ)+1)*((n : ℝ)+1/2)*monic n x := by
  have h := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℝ) x)
    (monicLaguerreHalf_recurrence n)
  norm_num [monic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_natCast,
    map_div₀] at h ⊢
  linear_combination h

private theorem monic_zero (x : ℝ) : monic 0 x = 1 := by
  simp [monic, monicLaguerreHalf]

private theorem monic_one (x : ℝ) : monic 1 x = x-1/2 := by
  norm_num [monic, monicLaguerreHalf]

/-- The monic Laguerre modes grow at least by a factor of D in the exterior region. -/
private theorem monic_grow {D n : ℕ} (hD : 0 < D) (hn : n < D)
    {x : ℝ} (hx : 4*(D : ℝ) ≤ x) :
    0 < monic n x ∧ (D : ℝ)*monic n x ≤ monic (n+1) x := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  induction n with
  | zero =>
    rw [monic_zero, monic_one]
    constructor <;> linarith
  | succ n ih =>
    obtain ⟨hpos,hgrow⟩ := ih (by omega)
    have hDn : (n : ℝ)+2 ≤ D := by exact_mod_cast (show n+2 ≤ D by omega)
    have hb : 0 < monic (n+1) x :=
      (mul_pos (by linarith) hpos).trans_le hgrow
    have hc : ((n : ℝ)+1)*((n : ℝ)+1/2) ≤ (D : ℝ)*D := by
      gcongr <;> linarith
    have hback : ((n : ℝ)+1)*((n : ℝ)+1/2)*monic n x ≤ (D : ℝ)*monic (n+1) x :=
      (mul_le_mul_of_nonneg_right hc hpos.le).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hgrow (by positivity))
    have hfront : 2*(D : ℝ)*monic (n+1) x ≤
        (x-(2*(n : ℝ)+5/2))*monic (n+1) x :=
      mul_le_mul_of_nonneg_right (by linarith) hb.le
    refine ⟨hb, ?_⟩
    rw [monic_succ_succ]
    linarith

noncomputable def positiveMode (n : ℕ) (x : ℝ) : ℝ :=
  monic n x / (n.factorial : ℝ)

theorem positiveMode_pos {D n : ℕ} (hD : 0 < D) (hn : n ≤ D)
    {x : ℝ} (hx : 4*(D : ℝ) ≤ x) : 0 < positiveMode n x := by
  apply div_pos _ (by positivity)
  by_cases h : n < D
  · exact (monic_grow hD h hx).1
  · have he : n = D := by omega
    subst n
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
    obtain ⟨ha,hb⟩ := monic_grow hD (Nat.lt_succ_self k) hx
    exact (mul_pos (by positivity) ha).trans_le hb

theorem positiveMode_step {D n : ℕ} (hD : 0 < D) (hn : n < D)
    {x : ℝ} (hx : 4*(D : ℝ) ≤ x) :
    (D : ℝ)*positiveMode n x ≤ ((n : ℝ)+1)*positiveMode (n+1) x := by
  have hp : (0 : ℝ) < n.factorial := by positivity
  have hs : (0 : ℝ) < (n : ℝ)+1 := by positivity
  simp only [positiveMode, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have h₁ : ((n : ℝ)+1)*(monic (n+1) x / (((n : ℝ)+1)*(n.factorial : ℝ))) =
      monic (n+1) x / (n.factorial : ℝ) := by field_simp
  rw [h₁, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (monic_grow hD hn hx).2 hp.le

theorem positiveMode_mono {D m n : ℕ} (hD : 0 < D) (hmn : m ≤ n) (hn : n ≤ D)
    {x : ℝ} (hx : 4*(D : ℝ) ≤ x) : positiveMode m x ≤ positiveMode n x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hb := positiveMode_step hD (by omega : n < D) hx
    have hp := (positiveMode_pos hD hn hx).le
    have hc : ((n : ℝ)+1) ≤ D := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right hc hp
    have hDr : (0 : ℝ) < D := by positivity
    exact (ih (by omega)).trans ((mul_le_mul_iff_right₀ hDr).mp (hb.trans hh))

theorem positiveMode_block {D m k : ℕ} (hD : 0 < D) (hi : m+k ≤ D)
    (hb : 4*((m+k : ℕ) : ℝ) ≤ 3*(D : ℝ)) {x : ℝ}
    (hx : 4*(D : ℝ) ≤ x) :
    positiveMode m x ≤ (3/4 : ℝ)^k * positiveMode (m+k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hidx : m+k < D := by omega
    have hprev : 4*((m+k : ℕ) : ℝ) ≤ 3*(D : ℝ) := by
      push_cast at hb ⊢
      linarith
    have hstep := positiveMode_step hD hidx hx
    have hp := (positiveMode_pos hD hi hx).le
    have hcoef : ((m+k : ℕ) : ℝ)+1 ≤ (3/4 : ℝ)*(D : ℝ) := by
      push_cast at hb ⊢
      linarith
    have hh := hstep.trans (mul_le_mul_of_nonneg_right hcoef hp)
    have hDr : (0 : ℝ) < D := by positivity
    have hs : positiveMode (m+k) x ≤ (3/4 : ℝ)*positiveMode (m+(k+1)) x :=
      (mul_le_mul_iff_right₀ hDr).mp (by convert hh using 1; ring)
    calc
      _ ≤ (3/4 : ℝ)^k * positiveMode (m+k) x := ih (by omega) hprev
      _ ≤ (3/4 : ℝ)^k * ((3/4 : ℝ)*positiveMode (m+(k+1)) x) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [pow_succ, mul_assoc]

theorem mode_even_eq (k : ℕ) (x : ℝ) : mode (2*k) x = positiveMode (2*k) x := by
  simp only [mode, positiveMode, monic, laguerreHalf, eval₂_mul, eval₂_C, map_div₀,
    map_pow, map_neg, map_one, map_natCast, pow_mul]
  norm_num
  ring

end NextProof.Exterior
