import NextProof.ExteriorSeries

namespace NextProof.Exterior

open Polynomial

private theorem originMode_succ (n : ℕ) :
    ((n : ℝ)+1)*mode (n+1) 0 = ((n : ℝ)+1/2)*mode n 0 := by
  induction n with
  | zero => norm_num [mode]
  | succ n ih =>
    have h := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℝ) 0)
      (laguerreHalf_recurrence n)
    norm_num [eval₂_sub, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_natCast,
      map_div₀] at h
    simp [mode, Nat.add_assoc] at ih ⊢
    linear_combination h + ih

def originNum (j : ℕ) : ℤ := (4*(j : ℤ)+1)*(4*(j : ℤ)+3)
def originDen (j : ℕ) : ℤ := (4*(j : ℤ)+2)*(4*(j : ℤ)+4)

private theorem originDen_pos (j : ℕ) : 0 < originDen j := by
  unfold originDen
  positivity

private theorem originNum_nonneg (j : ℕ) : 0 ≤ originNum j := by
  unfold originNum
  positivity

private theorem originMode_step (j : ℕ) :
    (originDen j : ℝ)*mode (2*(j+1)) 0 = (originNum j : ℝ)*mode (2*j) 0 := by
  have h1 := originMode_succ (2*j)
  have h2 := originMode_succ (2*j+1)
  have hidx : 2*(j+1) = 2*j+1+1 := by omega
  rw [hidx]
  unfold originNum originDen
  push_cast at h1 h2 ⊢
  linear_combination (4*(j : ℝ)+2)*2*h2 + (4*(j : ℝ)+3)*2*h1

/-- Both endpoints and the weighted upper sum are exact signed integers. -/
structure OriginState where
  lo : ℤ
  hi : ℤ
  acc : ℤ
  deriving DecidableEq, Repr

def originStep (j : ℕ) (w : ℤ) (s : OriginState) : OriginState :=
  ⟨originNum j * s.lo / originDen j,
   originNum j * s.hi / originDen j + 1,
   s.acc + w * (if w < 0 then s.lo else s.hi)⟩

def originRun (j : ℕ) : List ℤ → OriginState → OriginState
  | [], s => s
  | w::ws, s => originRun (j+1) ws (originStep j w s)

theorem originRun_append (j : ℕ) (a b : List ℤ) (s : OriginState) :
    originRun j (a ++ b) s = originRun (j+a.length) b (originRun j a s) := by
  induction a generalizing j s with
  | nil => simp [originRun]
  | cons w a ih =>
    rw [List.cons_append, originRun, originRun, ih]
    congr 1
    simp only [List.length_cons]
    omega

private theorem below_div_hi (a b : ℤ) (hb : 0 < b) :
    a ≤ (a/b+1)*b := by
  exact (Int.lt_ediv_add_one_mul_self a hb).le

private theorem originStep_bounds (E : ℝ) (j : ℕ) (w : ℤ) (s : OriginState)
    (hlo : (s.lo : ℝ) ≤ E*mode (2*j) 0) (hhi : E*mode (2*j) 0 ≤ s.hi) :
    ((originStep j w s).lo : ℝ) ≤ E*mode (2*(j+1)) 0 ∧
      E*mode (2*(j+1)) 0 ≤ (originStep j w s).hi := by
  have hd := originDen_pos j
  have hd' : (0 : ℝ) < originDen j := by exact_mod_cast hd
  have hn' : (0 : ℝ) ≤ originNum j := by exact_mod_cast originNum_nonneg j
  have h₁ : ((originNum j*s.lo/originDen j : ℤ) : ℝ) * (originDen j : ℝ) ≤
      (originNum j : ℝ)*(s.lo : ℝ) := by
    exact_mod_cast Int.ediv_mul_le (originNum j*s.lo) hd.ne'
  have h₂ : (originNum j : ℝ)*(s.hi : ℝ) ≤
      ((originNum j*s.hi/originDen j+1 : ℤ) : ℝ) * (originDen j : ℝ) := by
    exact_mod_cast below_div_hi (originNum j*s.hi) (originDen j) hd
  have hm := originMode_step j
  constructor
  · apply (mul_le_mul_iff_left₀ hd').mp
    have h := h₁.trans (mul_le_mul_of_nonneg_left hlo hn')
    calc
      _ ≤ (originNum j : ℝ) * (E * mode (2*j) 0) := h
      _ = E * mode (2*(j+1)) 0 * (originDen j : ℝ) := by linear_combination -E * hm
  · apply (mul_le_mul_iff_left₀ hd').mp
    calc
      _ = (originNum j : ℝ) * (E * mode (2*j) 0) := by linear_combination E * hm
      _ ≤ _ := (mul_le_mul_of_nonneg_left hhi hn').trans h₂

theorem originRun_sound (E : ℝ) (j : ℕ) (ws : List ℤ) (s : OriginState)
    (hlo : (s.lo : ℝ) ≤ E*mode (2*j) 0) (hhi : E*mode (2*j) 0 ≤ s.hi) :
    E*(series j ws).eval₂ (algebraMap ℚ ℝ) 0 + (s.acc : ℝ) ≤
      (originRun j ws s).acc := by
  induction ws generalizing j s with
  | nil => simp [series, originRun]
  | cons w ws ih =>
    obtain ⟨hlo',hhi'⟩ := originStep_bounds E j w s hlo hhi
    have hrest := ih (j+1) (originStep j w s) hlo' hhi'
    have hweight :
        (w : ℝ)*(E*mode (2*j) 0) ≤
          (w : ℝ) * ((if w < 0 then s.lo else s.hi : ℤ) : ℝ) := by
      split
      · exact mul_le_mul_of_nonpos_left hlo (by exact_mod_cast (le_of_lt ‹w < 0›))
      · exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast (le_of_not_gt ‹¬ w < 0›))
    rw [eval_series_cons, originRun]
    simp only [originStep, Int.cast_add, Int.cast_mul] at hrest ⊢
    linear_combination hrest + hweight

/-- A finite exact integer computation gives a rational upper bound at the origin. -/
theorem origin_le (den scale : ℕ) (ws : List ℤ)
    (hd : 0 < den) (hs : 0 < scale) :
    (witness den ws).eval₂ (algebraMap ℚ ℝ) 0 ≤
      ((originRun 0 ws ⟨scale,scale,0⟩).acc : ℝ) / ((den : ℝ)*(scale : ℝ)) := by
  have hbase : mode 0 0 = 1 := by simp [mode]
  have h := originRun_sound (scale : ℝ) 0 ws ⟨scale,scale,0⟩
    (by simp [hbase]) (by simp [hbase])
  simp only [Int.cast_zero, add_zero] at h
  have hd' : (0 : ℝ) < den := by exact_mod_cast hd
  rw [eval_witness, le_div_iff₀ (by positivity)]
  calc
    _ = (scale : ℝ)*(series 0 ws).eval₂ (algebraMap ℚ ℝ) 0 := by
      field_simp
    _ ≤ _ := h

/-- An exact negative upper sum implies strict negativity at the origin. -/
theorem origin_negative (den scale : ℕ) (ws : List ℤ)
    (hd : 0 < den) (hs : 0 < scale)
    (hc : (originRun 0 ws ⟨scale,scale,0⟩).acc < 0) :
    (witness den ws).eval₂ (algebraMap ℚ ℝ) 0 < 0 := by
  have hc' : ((originRun 0 ws ⟨scale,scale,0⟩).acc : ℝ) < 0 := by exact_mod_cast hc
  exact (origin_le den scale ws hd hs).trans_lt (div_neg_of_neg_of_pos hc' (by positivity))

end NextProof.Exterior
