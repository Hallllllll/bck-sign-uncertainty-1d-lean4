import NextProof.FourierLaguerre
import NextProof.DualKernel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Soundness of a positive quadrature obstruction on the finite even Laguerre span. -/

namespace NextProof.Dual

open Polynomial

noncomputable def realMode (n : ℕ) : ℝ[X] := (laguerreHalf n).map (algebraMap ℚ ℝ)

/-- Index `d` is inclusive. The highest Laguerre degree is `2*d`. -/
noncomputable def evenPolynomial (d : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d+1), C (a k) * realMode (2*k)

private lemma natDegree_monic_le (n : ℕ) : (monicLaguerreHalf n).natDegree ≤ n := by
  induction n with
  | zero => simp [monicLaguerreHalf]
  | succ n ih =>
    rw [monicLaguerreHalf]
    apply (natDegree_sub_le ..).trans
    apply max_le
    · exact (natDegree_mul_le_of_le ((natDegree_sub_le ..).trans (max_le natDegree_X_le (by simp))) ih).trans
        (by omega)
    · exact (natDegree_mul_le_of_le natDegree_X_le
        ((natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans ih))).trans (by omega)

theorem natDegree_evenPolynomial_le (d : ℕ) (a : ℕ → ℝ) :
    (evenPolynomial d a).natDegree ≤ 2*d := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have h := Finset.mem_range.mp hk
  exact (natDegree_C_mul_le ..).trans (natDegree_map_le.trans
    ((natDegree_C_mul_le ..).trans ((natDegree_monic_le _).trans (by omega))))

private lemma realMode_recurrence (n : ℕ) (t : ℝ) :
    ((n : ℝ)+2) * (realMode (n+2)).eval t =
      (2*(n : ℝ)+5/2-t) * (realMode (n+1)).eval t -
      ((n : ℝ)+1/2) * (realMode n).eval t := by
  have h := congrArg (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℝ) t) (laguerreHalf_recurrence n)
  simpa [realMode, eval_map] using h

private noncomputable def scaledMode (q : ℤ) (t : ℝ) (n : ℕ) : ℝ :=
  (2*(q : ℝ))^n * (n.factorial : ℝ) * (realMode n).eval t

private lemma scaledMode_step (q y : ℤ) (hq : 0 < q) (n : ℕ) :
    scaledMode q (y/q : ℝ) (n+2) =
      ((4*(n : ℝ)+5)*q-2*y) * scaledMode q (y/q : ℝ) (n+1) -
      ((2*(n : ℝ)+2)*(2*(n : ℝ)+1))*(q : ℝ)^2 * scaledMode q (y/q : ℝ) n := by
  let t : ℝ := y / q
  change scaledMode q t (n+2) = _ * scaledMode q t (n+1) - _ * scaledMode q t n
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hy : (y : ℝ) = (q : ℝ)*t := by dsimp [t]; field_simp
  simp only [scaledMode, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [hy]
  linear_combination 4*(q : ℝ)^2*(2*(q : ℝ))^n*(n.factorial : ℝ)*((n : ℝ)+1) *
    realMode_recurrence n t

noncomputable def weightedEval (q : ℤ) (r : List (ℤ × ℤ)) (p : ℝ[X]) : ℝ :=
  (r.map fun u => (u.2 : ℝ) * p.eval ((u.1 : ℝ)/q)).sum

private theorem weightedEval_sum (q : ℤ) (r : List (ℤ × ℤ)) (d : ℕ) (a : ℕ → ℝ) :
    weightedEval q r (evenPolynomial d a) =
      ∑ k ∈ Finset.range (d+1), a k * weightedEval q r (realMode (2*k)) := by
  induction r with
  | nil => simp [weightedEval]
  | cons u r ih =>
    simp only [weightedEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [evenPolynomial, eval_finsetSum, eval_mul, eval_C, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring

/-- Real quadrature exactness and more nodes than the degree force vanishing. -/
theorem eq_zero_of_quadrature (q : ℤ) (r : List (ℤ × ℤ)) (d : ℕ) (τ W : ℝ)
    (hq : 0 < q) (hW : 0 < W) (hw : ∀ u ∈ r, 0 < u.2)
    (hnodes : ∀ u ∈ r, τ ≤ (u.1 : ℝ)/q)
    (hcard : 2*d < (r.map Prod.fst).toFinset.card)
    (hmodes : ∀ k ≤ d, weightedEval q r (realMode (2*k)) = W * (realMode (2*k)).eval 0)
    (a : ℕ → ℝ) (horigin : (evenPolynomial d a).eval 0 ≤ 0)
    (htail : ∀ t : ℝ, τ ≤ t → 0 ≤ (evenPolynomial d a).eval t) :
    evenPolynomial d a = 0 := by
  let p := evenPolynomial d a
  have hexact : weightedEval q r p = W * p.eval 0 := by
    rw [weightedEval_sum]
    simp only [p, evenPolynomial, eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmodes k (by have := Finset.mem_range.mp hk; omega)]
    ring
  let term (u : ℤ × ℤ) := (u.2 : ℝ) * p.eval ((u.1 : ℝ)/q)
  have hterm : ∀ z ∈ r.map term, 0 ≤ z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (by exact_mod_cast (hw u hu).le) (htail _ (hnodes u hu))
  have hsum : (r.map term).sum ≤ 0 :=
    hexact.le.trans (mul_nonpos_of_nonneg_of_nonpos hW.le horigin)
  let S := (r.map Prod.fst).toFinset
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (ι := S)
    (f := fun i => ((i.val : ℤ) : ℝ)/q)
  · intro i j hij
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    apply Subtype.ext
    exact_mod_cast (div_left_inj₀ hq').mp hij
  · intro i
    have hi := List.mem_toFinset.mp i.property
    obtain ⟨u, hu, huy⟩ := List.mem_map.mp hi
    have hz : term u = 0 := le_antisymm
      ((List.single_le_sum hterm _ (List.mem_map_of_mem hu)).trans hsum)
      (hterm _ (List.mem_map_of_mem hu))
    have hw' : (u.2 : ℝ) ≠ 0 := by exact_mod_cast (hw u hu).ne'
    rw [← huy]
    exact (mul_eq_zero.mp hz).resolve_left hw'
  · exact (natDegree_evenPolynomial_le d a).trans_lt (hcard.trans_eq (Fintype.card_coe S).symm)

/-- The integer recurrence simultaneously evaluates two consecutive scaled Laguerre modes. -/
theorem pair_cast (q y : ℤ) (hq : 0 < q) (n : ℕ) :
    (((pair q y n).1 : ℝ) =
      (2*(q : ℝ))^n * (n.factorial : ℝ) * (realMode n).eval ((y : ℝ)/q)) ∧
    (((pair q y n).2 : ℝ) = (2*(q : ℝ))^(n+1) * ((n+1).factorial : ℝ) *
      (realMode (n+1)).eval ((y : ℝ)/q)) := by
  change ((pair q y n).1 : ℝ) = scaledMode q (y/q : ℝ) n ∧
    ((pair q y n).2 : ℝ) = scaledMode q (y/q : ℝ) (n+1)
  induction n with
  | zero =>
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simp [pair, scaledMode, realMode, laguerreHalf_zero, laguerreHalf_one]
    field_simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [scaledMode_step q y hq n]
    change (((((4*(n:ℤ)+5)*q-2*y)*(pair q y n).2 -
      ((2*(n:ℤ)+2)*(2*(n:ℤ)+1))*q^2*(pair q y n).1 : ℤ) : ℝ)) = _
    push_cast
    rw [ih.1, ih.2]

private theorem moment_cast (q : ℤ) (hq : 0 < q) (r : Rule) (k : ℕ) :
    (moment q r k : ℝ) = ((2*(q : ℝ))^(2*k) * ((2*k).factorial : ℝ)) *
      weightedEval q r (realMode (2*k)) := by
  induction r with
  | nil => simp [moment, weightedEval]
  | cons u r ih =>
    change (((u.2 * (pair q u.1 (2*k)).1 + moment q r k : ℤ) : ℝ)) =
      _ * ((u.2 : ℝ) * _ + weightedEval q r (realMode (2*k)))
    push_cast
    rw [(pair_cast q u.1 hq (2*k)).1, ih]
    ring

theorem weightedEval_of_moment {q : ℤ} {r : Rule} (hq : 0 < q) (k : ℕ)
    (h : moment q r k = total r * (pair q 0 (2*k)).1) :
    weightedEval q r (realMode (2*k)) = (total r : ℝ) * (realMode (2*k)).eval 0 := by
  have hh := congrArg (fun z : ℤ => (z : ℝ)) h
  change (moment q r k : ℝ) = ((total r * (pair q 0 (2*k)).1 : ℤ) : ℝ) at hh
  rw [moment_cast _ hq, Int.cast_mul, (pair_cast q 0 hq (2*k)).1] at hh
  simp only [Int.cast_zero, zero_div] at hh
  have hp : 0 < (2*(q : ℝ))^(2*k) * ((2*k).factorial : ℝ) := by
    have : 0 < (q : ℝ) := by exact_mod_cast hq
    positivity
  apply mul_left_cancel₀ hp.ne'
  rw [hh]
  ring

/-- Raw integer moment equalities exclude every nonzero admissible polynomial in the span. -/
theorem eq_zero_of_moments (q : ℤ) (r : Rule) (d : ℕ) (τ : ℝ)
    (hq : 0 < q) (hW : 0 < total r) (hw : ∀ u ∈ r, 0 < u.2)
    (hnodes : ∀ u ∈ r, τ ≤ (u.1 : ℝ)/q)
    (hcard : 2*d < (r.map Prod.fst).toFinset.card)
    (hmom : ∀ k ≤ d, moment q r k = total r * (pair q 0 (2*k)).1)
    (a : ℕ → ℝ) (horigin : (evenPolynomial d a).eval 0 ≤ 0)
    (htail : ∀ t : ℝ, τ ≤ t → 0 ≤ (evenPolynomial d a).eval t) :
    evenPolynomial d a = 0 :=
  eq_zero_of_quadrature q r d τ (total r) hq (by exact_mod_cast hW) hw hnodes hcard
    (fun k hk => weightedEval_of_moment hq k (hmom k hk)) a horigin htail

private theorem nodup_eraseDups (l : List ℤ) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons y ys =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp [List.mem_eraseDups], nodup_eraseDups _⟩
termination_by l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem card_nodes_eq_eraseDups (l : List ℤ) : l.toFinset.card = l.eraseDups.length := by
  rw [← List.toFinset_card_of_nodup (nodup_eraseDups l)]
  congr 1
  ext y
  simp [List.mem_eraseDups]

/-- Degree-226 specialization in the exact integer grid and node-count format. -/
theorem degree226_obstruction (r : Rule)
    (hW : 0 < total r) (hw : ∀ u ∈ r, 0 < u.2) (hnodes : ∀ u ∈ r, 1910 < u.1)
    (hcard : 226 < (r.map Prod.fst).eraseDups.length)
    (hmom : ∀ k ≤ 113, moment 1000 r k = total r * (pair 1000 0 (2*k)).1)
    (a : ℕ → ℝ) (horigin : (evenPolynomial 113 a).eval 0 ≤ 0)
    (htail : ∀ t : ℝ, 191/100 ≤ t → 0 ≤ (evenPolynomial 113 a).eval t) :
    evenPolynomial 113 a = 0 := by
  apply eq_zero_of_moments 1000 r 113 (191/100) (by decide) hW hw _ _ hmom a horigin htail
  · intro u hu
    have h : (1910 : ℝ) < (u.1 : ℝ) := by exact_mod_cast hnodes u hu
    norm_num
    linarith
  · rwa [card_nodes_eq_eraseDups]

theorem moment_append_of_exact {q : ℤ} {r s : Rule} {k : ℕ}
    (hr : moment q r k = total r * (pair q 0 (2*k)).1)
    (hs : moment q s k = total s * (pair q 0 (2*k)).1) :
    moment q (r ++ s) k = total (r ++ s) * (pair q 0 (2*k)).1 := by
  unfold moment
  simp only [List.map_append, List.sum_append, total, add_mul]
  exact congrArg₂ (· + ·) hr hs

/-- Direct specialization to two separately checked integer tables. -/
theorem degree226_of_two_checks (r s : Rule)
    (hr : check 1000 r 114 = true) (hs : check 1000 s 114 = true)
    (hW : 0 < total (r ++ s)) (hw : ∀ u ∈ r ++ s, 0 < u.2)
    (hnodes : ∀ u ∈ r ++ s, 1910 < u.1)
    (hcard : 226 < ((r ++ s).map Prod.fst).eraseDups.length)
    (a : ℕ → ℝ) (horigin : (evenPolynomial 113 a).eval 0 ≤ 0)
    (htail : ∀ t : ℝ, 191/100 ≤ t → 0 ≤ (evenPolynomial 113 a).eval t) :
    evenPolynomial 113 a = 0 :=
  degree226_obstruction (r ++ s) hW hw hnodes hcard
    (fun k hk => moment_append_of_exact (check_sound hr k (by omega))
      (check_sound hs k (by omega))) a horigin htail

/-- Direct API for a combined table: the three finite checks discharge all certificate hypotheses. -/
theorem degree226_of_check (r : Rule)
    (hc : check 1000 r 114 = true)
    (hb : ∀ u ∈ r, 1910 < u.1 ∧ 0 < u.2)
    (hn : 226 < (r.map Prod.fst).toFinset.card)
    (a : ℕ → ℝ) (horigin : (evenPolynomial 113 a).eval 0 ≤ 0)
    (htail : ∀ t : ℝ, 191/100 ≤ t → 0 ≤ (evenPolynomial 113 a).eval t) :
    evenPolynomial 113 a = 0 := by
  have hW : 0 < total r := by
    cases r with
    | nil => simp at hn
    | cons u us =>
      change 0 < u.2 + (us.map Prod.snd).sum
      apply add_pos_of_pos_of_nonneg (hb u List.mem_cons_self).2
      apply List.sum_nonneg
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact (hb v (List.mem_cons_of_mem _ hv)).2.le
  exact degree226_obstruction r hW (fun u hu => (hb u hu).2) (fun u hu => (hb u hu).1)
    (by rwa [← card_nodes_eq_eraseDups]) (fun k hk => check_sound hc k (by omega))
    a horigin htail

end NextProof.Dual

#print axioms NextProof.Dual.degree226_of_check

