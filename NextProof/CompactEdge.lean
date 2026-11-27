import NextProof.CompactHalf

namespace NextProof.Compact
open NextProof.Tail Polynomial

theorem hom_bound_zero_le (w : List ℤ) : homBound 0 w ≤ 2^w.length*absSum w := by
  induction w with
  | nil => simp [homBound,absSum]
  | cons a as ih =>
    have hpos : 0 ≤ absSum as := by
      exact_mod_cast (abs_nonneg (horner (0:ℝ) as)).trans (tail_bound as 0 (by norm_num) (by norm_num))
    have hp : (0:ℤ) ≤ 2^as.length := by positivity
    simp only [homBound,absSum,List.length_cons,abs_zero,zero_add,one_mul,pow_succ]
    nlinarith only [ih,mul_nonneg hp hpos]

private theorem plain_bound (u : List ℤ) :
    Bounded (horner (X : ℤ[X]) u) (absSum u) := by
  simpa only [map_zero,zero_add,abs_zero,major_one] using horner_bound 0 u

/-- A residual shift identity checked at a single safe radix gives a genuine
polynomial identity. The input and output vectors can be independently sharded. -/
theorem edge_identity {parent child residual : Blocks} {s K B : ℤ}
    (hs : s=0 ∨ s=1) (hK : 0 ≤ K) (hB : 0<B)
    (hbound : 2^parent.size*absSum parent.list +
      (K*absSum child.list+absSum residual.list) < B)
    (hv : fastHom s B parent = K*child.subst B+residual.subst B) :
    halfForm (X:ℤ[X]) (C s) parent.list =
    C K * horner X child.list + horner X residual.list := by
  have hmajor : homBound s parent.list ≤ 2^parent.size*absSum parent.list := by
    rcases hs with rfl|rfl
    · simpa [Blocks.size_eq] using hom_bound_zero_le parent.list
    · rw [hom_bound_one,Blocks.size_eq]
  apply packed_eq (hom_bound s parent.list)
    (bound_add (bound_smul K (plain_bound child.list)) (plain_bound residual.list)) hB
  · rw [abs_of_nonneg hK]
    linarith
  · simpa only [half_eval_int,eval_X,eval_C,eval_add,eval_mul,horner_eval,fastHom_spec,
       Blocks.subst_eq] using hv

theorem edge_cover {parent child residual : Blocks} {s K : ℤ}
    (h : halfForm (X:ℤ[X]) (C s) parent.list =
      C K * horner X child.list + horner X residual.list)
    (hK : 0 ≤ K) (he : 0 ≤ unitLower residual.list)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hc : 0 ≤ horner x child.list) :
    0 ≤ horner ((x+s)/2) parent.list := by
  have hval := congrArg (fun p : ℤ[X] => p.eval₂ (Int.castRingHom ℝ) x) h
  simp only [half_eval_real,eval₂_C,eval₂_X,eval₂_add,eval₂_mul,horner_real,half_value] at hval
  change (2:ℝ)^parent.list.length * horner ((x+(s:ℝ))/2) parent.list =
    (K:ℝ)*horner x child.list + horner x residual.list at hval
  have hr := (show (0:ℝ) ≤ (unitLower residual.list:ℝ) by exact_mod_cast he).trans
    (unitLower_le _ hx hx')
  apply nonneg_of_mul_nonneg_right (a:= (2:ℝ)^parent.list.length) _ (by positivity)
  rw [hval]
  exact add_nonneg (mul_nonneg (by exact_mod_cast hK) hc) hr

def Covers (cut : ℚ) (w : Blocks) :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (cut:ℝ) ≤ x → 0 ≤ horner x w.list

theorem cover_skip {t : ℚ} {w : Blocks} (h : 1<t) : Covers t w := by
  intro x _ hx ht
  have h' : (1:ℝ) < t := by exact_mod_cast h
  linarith

theorem cover_leaf {t : ℚ} {w : Blocks} (h : 0 ≤ unitLower w.list) : Covers t w :=
  fun x hx hx' _ => (show (0:ℝ) ≤ (unitLower w.list:ℝ) by exact_mod_cast h).trans
    (unitLower_le _ hx hx')

theorem cover_join {t : ℚ} {w : Blocks}
    (hl : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (2*t:ℝ) ≤ u → 0 ≤ horner (u/2) w.list)
    (hr : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (2*t-1:ℝ) ≤ u → 0 ≤ horner ((u+1)/2) w.list) :
    Covers t w := by
  intro x hx hx' ht
  by_cases h : x ≤ 1/2
  · have hh := hl (2*x) (by linarith) (by linarith) (by linarith)
    simpa using hh
  · have hh := hr (2*x-1) (by linarith) (by linarith) (by linarith)
    convert hh using 2; ring

def Branch (s : ℤ) (cut : ℚ) (w : Blocks) :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ((2*cut-(s:ℚ):ℚ):ℝ) ≤ x → 0 ≤ horner ((x+s)/2) w.list

theorem branch_skip {t : ℚ} {w : Blocks} {s : ℤ} (h : 1 < 2*t-(s:ℚ)) : Branch s t w := by
  intro x hx hx' hc
  have h' : (1:ℝ) < ((2*t-(s:ℚ):ℚ):ℝ) := by exact_mod_cast h
  linarith

theorem branch_checked {parent child residual : Blocks} {s K : ℤ} {t : ℚ}
    (id : halfForm (X:ℤ[X]) (C s) parent.list =
      C K * horner X child.list + horner X residual.list)
    (hK : 0 ≤ K) (he : 0 ≤ unitLower residual.list)
    (hc : Covers (2*t-(s:ℚ)) child) : Branch s t parent :=
  fun x hx hx' ht => edge_cover id hK he x hx hx' (hc x hx hx' ht)

theorem join_branches {t : ℚ} {w : Blocks} (l : Branch 0 t w) (r : Branch 1 t w) : Covers t w := by
  apply cover_join
  · intro x hx hx' ht
    simpa using l x hx hx' (by push_cast; linarith)
  · intro x hx hx' ht
    simpa using r x hx hx' (by push_cast; linarith)

theorem branch_left_normalized {p c : Blocks} {t : ℚ} {k m : ℕ}
    (hn : truncate m (quotient (2^k) (leftAux 1 p.list)) = c.list)
    (hc : Covers (2*t-((0:ℤ):ℚ)) c) : Branch 0 t p := by
  intro x hx hx' ht
  have h0 := hc x hx hx' ht
  rw [← hn] at h0
  have h1 := h0.trans (truncate_le m (quotient (2^k) (leftAux 1 p.list)) x hx hx')
  have h2 := (mul_nonneg (show 0 ≤ ((2^k:ℤ):ℝ) by positivity) h1).trans
    (quotient_le (2^k) (by positivity) (leftAux 1 p.list) x hx)
  have hh := leftAux_le p.list 1 (by decide) x hx
  simpa using h2.trans (by simpa using hh : horner x (leftAux 1 p.list) ≤ horner (x/2) p.list)

end NextProof.Compact
