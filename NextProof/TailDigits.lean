import NextProof.TailPacked

namespace NextProof.Tail
open Polynomial

/-- Nearest-integer quotient and centered remainder. At the radix used below
every actual digit has absolute value strictly less than half the radix. -/
def upperPart (b z : ℤ) := (z+b/2)/b
def lowerPart (b z : ℤ) := (z+b/2)%b-b/2

private theorem parts {b r q : ℤ} (hb : 0 < b) (hr : 2*|r| < b) :
    upperPart b (r+b*q) = q ∧ lowerPart b (r+b*q) = r := by
  have hn := neg_abs_le r
  have hp := le_abs_self r
  have hl : 0 ≤ r+b/2 := by omega
  have hh : r+b/2 < b := by omega
  simp only [upperPart, lowerPart, show r+b*q+b/2 = (r+b/2)+b*q by ring,
    Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt hl hh, zero_add,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt hl hh, add_sub_cancel_right, and_self]

private noncomputable def dropP (p : ℤ[X]) : ℕ → ℤ[X]
  | 0 => p
  | j+1 => dropP p.divX j

private theorem dropP_coeff (p : ℤ[X]) (j i : ℕ) : (dropP p j).coeff i = p.coeff (i+j) := by
  induction j generalizing p with
  | zero => simp [dropP]
  | succ j ih => rw [dropP, ih, coeff_divX]; rfl

private theorem eval_split (p : ℤ[X]) (B : ℤ) (hB : 0 < B)
    (hb : ∀ i, 2*|p.coeff i| < B) (j : ℕ) :
    ∃ r : ℤ, 2*|r| < B^j ∧ p.eval B = r+B^j*(dropP p j).eval B := by
  induction j generalizing p with
  | zero => exact ⟨0, by simp, by simp [dropP]⟩
  | succ j ih =>
    obtain ⟨r,hr,he⟩ := ih p.divX (fun i => by simpa only [coeff_divX] using hb (i+1))
    refine ⟨p.coeff 0+B*r, ?_, ?_⟩
    · have h1 := abs_add_le (p.coeff 0) (B*r)
      rw [abs_mul, abs_of_pos hB] at h1
      have h2 := mul_le_mul_of_nonneg_left (show 2*|r| ≤ B^j-1 by omega) hB.le
      rw [pow_succ]
      linarith only [h1,h2,hb 0]
    · have h := congrArg (eval B) (divX_mul_X_add p)
      simp only [eval_add, eval_mul, eval_X, eval_C] at h
      rw [← h, he, pow_succ, dropP]; ring

/-- Random-access signed digit. The argument z is the packed value at the radix. -/
def packedDigit (B z : ℤ) (j : ℕ) := lowerPart B (upperPart (B^j) z)

theorem packedDigit_eval (p : ℤ[X]) (B : ℤ) (hB : 0 < B)
    (hb : ∀ i, 2*|p.coeff i| < B) (j : ℕ) :
    packedDigit B (p.eval B) j = p.coeff j := by
  obtain ⟨r,hr,he⟩ := eval_split p B hB hb j
  rw [packedDigit, he, (parts (pow_pos hB j) hr).1]
  have hx := congrArg (eval B) (divX_mul_X_add (dropP p j))
  simp only [eval_add, eval_mul, eval_X, eval_C] at hx
  have he' : (dropP p j).eval B = p.coeff j + B * (dropP p j).divX.eval B := by
    rw [← hx, dropP_coeff, zero_add]; ring
  rw [he', (parts hB (hb j)).2]

/-- A power-of-two radix sized from a provable coefficient bound. -/
def radix (a : Blocks) : ℤ := 2^((a.absBlocks.subst 2).natAbs.log2+3)

theorem radix_big (a : Blocks) : 2*a.absBlocks.subst 2 < radix a := by
  let t := (a.absBlocks.subst 2).natAbs
  have ht : t < 2^(t.log2+1) := Nat.lt_log2_self
  have h : a.absBlocks.subst 2 ≤ (t : ℤ) := by
    simpa only [t, Int.natCast_natAbs] using le_abs_self (a.absBlocks.subst 2)
  have hh : (t : ℤ) < 2^(t.log2+1) := by exact_mod_cast ht
  change _ < (2:ℤ)^(t.log2+3)
  rw [show t.log2+3=t.log2+1+2 by omega, pow_add]
  nlinarith [pow_pos (by decide : (0:ℤ)<2) (t.log2+1)]

def shiftedDigit (a : Blocks) (j : ℕ) : ℤ := packedDigit (radix a) (a.subst (1+radix a)) j

theorem shiftedDigit_correct (a : Blocks) (j : ℕ) :
    shiftedDigit a j = (horner (1+X : ℤ[X]) a.list).coeff j := by
  have h := horner_bound 1 a.list
  have b := radix_big a
  rw [Blocks.major_eq] at b
  simp only [map_one, abs_one, one_add_one_eq_two] at h
  have val := horner_eval (1+X : ℤ[X]) a.list (radix a)
  simp only [eval_add, eval_X, eval_one] at val
  rw [shiftedDigit, Blocks.subst_eq, ← val]
  apply packedDigit_eval _ _ (by unfold radix; positivity)
  intro i
  linarith [h i]

def shiftedVector (a : Blocks) : List ℤ := (List.range a.size).map (shiftedDigit a)

private theorem coeff_vanish (xs : List ℤ) (j : ℕ) (hj : xs.length ≤ j) :
    (horner (1+X : ℤ[X]) xs).coeff j = 0 := by
  induction xs generalizing j with
  | nil => simp [horner]
  | cons w xs ih =>
    cases j with
    | zero => simp at hj
    | succ j =>
      have h : xs.length ≤ j := by simpa using hj
      rw [horner, add_mul, one_mul, coeff_add, coeff_add, coeff_X_mul,
        ih j h, ih (j+1) (by omega), ← C_eq_intCast, coeff_C_succ]
      simp

private theorem coeff_list (xs : List ℤ) (j : ℕ) :
    (horner (X : ℤ[X]) xs).coeff j = xs.getD j 0 := by
  induction xs generalizing j with
  | nil => simp [horner, List.getD]
  | cons w xs ih =>
    rw [horner, ← C_eq_intCast, coeff_add]
    cases j with
    | zero => rw [coeff_C_zero, coeff_X_mul_zero, add_zero]; rfl
    | succ j => rw [coeff_C_succ, coeff_X_mul, zero_add, ih]; rfl

/-- An unconditional computable Taylor translation. No supplied array or arithmetic
hypothesis is needed; the signed digits are the coefficients by the radix bound. -/
theorem shiftedVector_identity (a : Blocks) :
    horner (C 1+X : ℤ[X]) a.list = horner X (shiftedVector a) := by
  ext j
  rw [coeff_list, C_1]
  by_cases h : j < a.size
  · simp [shiftedVector, List.getD, h, shiftedDigit_correct]
  · rw [coeff_vanish _ _ (by simpa only [← Blocks.size_eq] using Nat.le_of_not_gt h)]
    simp [shiftedVector, List.getD, h]

end NextProof.Tail
