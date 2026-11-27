import NextProof.CompactEdge

namespace NextProof.Compact
open NextProof.Tail Polynomial

/-- Distinct integer roots give a divisor of the constant coefficient even
when the integers themselves have common prime factors. -/
private theorem rootProductDvd (points : List ℤ) (hn : points.Nodup)
    (p : ℤ[X]) (hz : ∀ x ∈ points, p.eval x = 0) : points.prod ∣ p.coeff 0 := by
  induction points generalizing p with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr (show p.IsRoot a from hz a (by simp))
    have hq (x : ℤ) (hx : x ∈ xs) : q.eval x = 0 := by
      have he := hz x (List.mem_cons_of_mem _ hx)
      simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at he
      exact he.resolve_left (fun e => ha (e ▸ hx))
    obtain ⟨k, hk⟩ := ih hn q hq
    refine ⟨-k, ?_⟩
    simp only [List.prod_cons, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, hk]
    ring

theorem eq_zero_of_eval_shards (points : List ℤ) (hn : points.Nodup)
    (hp : ∀ x ∈ points, 0 < x) (p : ℤ[X])
    (hm : ∀ i, |p.coeff i| < points.prod) (hz : ∀ x ∈ points, p.eval x = 0) :
    p = 0 := by
  ext i
  simp only [coeff_zero]
  induction i generalizing p with
  | zero => exact Int.eq_zero_of_abs_lt_dvd (rootProductDvd points hn p hz) (hm 0)
  | succ i ih =>
    have h0 := Int.eq_zero_of_abs_lt_dvd (rootProductDvd points hn p hz) (hm 0)
    rw [← coeff_divX]
    apply ih (p := p.divX) (fun j => by simpa only [coeff_divX] using hm (j+1))
    intro x hx
    have he := congrArg (eval x) (divX_mul_X_add p)
    simp only [eval_add, eval_mul, eval_X, eval_C, h0, add_zero, hz x hx] at he
    exact (mul_eq_zero.mp he).resolve_right (hp x hx).ne'

/-- Reconstruct the exact scalar obligation for Compact.edge_identity from
independently checked evaluations at smaller radices. -/
theorem edge_scalar_of_shards {parent child residual : Blocks} {s K : ℤ}
    (hs : s=0 ∨ s=1) (hK : 0 ≤ K)
    (points : List ℤ) (hn : points.Nodup) (hp : ∀ x ∈ points, 0 < x)
    (hbound : 2^parent.size*absSum parent.list +
      (K*absSum child.list+absSum residual.list) < points.prod)
    (checks : ∀ x ∈ points, fastHom s x parent = K*child.subst x+residual.subst x)
    (B : ℤ) : fastHom s B parent = K*child.subst B+residual.subst B := by
  let p := halfForm (X:ℤ[X]) (C s) parent.list
  let q := C K * horner (X:ℤ[X]) child.list + horner X residual.list
  have major : homBound s parent.list ≤ 2^parent.size*absSum parent.list := by
    rcases hs with rfl | rfl
    · simpa only [Blocks.size_eq] using hom_bound_zero_le parent.list
    · rw [hom_bound_one, Blocks.size_eq]
  have plain (u : List ℤ) : Bounded (horner (X : ℤ[X]) u) (absSum u) := by
    simpa only [map_zero, zero_add, abs_zero, major_one] using horner_bound 0 u
  have hq := bound_add (bound_smul K (plain child.list)) (plain residual.list)
  rw [abs_of_nonneg hK] at hq
  have he : p-q = 0 := by
    apply eq_zero_of_eval_shards points hn hp
    · intro j
      rw [coeff_sub]
      exact ((abs_sub _ _).trans (add_le_add (hom_bound s parent.list j) (hq j))).trans_lt
        ((add_le_add major le_rfl).trans_lt hbound)
    · intro x hx
      simpa only [p,q,eval_sub,sub_eq_zero,half_eval_int,eval_X,eval_C,eval_add,
        eval_mul,horner_eval,fastHom_spec,Blocks.subst_eq] using checks x hx
  have hv := congrArg (eval B) (sub_eq_zero.mp he)
  simpa only [p,q,half_eval_int,eval_X,eval_C,eval_add,eval_mul,horner_eval,
    fastHom_spec,Blocks.subst_eq] using hv

end NextProof.Compact
