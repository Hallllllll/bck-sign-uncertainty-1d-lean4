import NextProof.CompactEdge

namespace NextProof.Compact.LeftKernel

open NextProof.Tail

/-- The first coefficient of the right input starts at exponent `xs.length`. -/
theorem leftAux_append (d : ℤ) (xs ys : List ℤ) :
    leftAux d (xs ++ ys) =
      leftAux d xs ++ leftAux ((2 : ℤ) ^ xs.length * d) ys := by
  induction xs generalizing d with
  | nil => simp [leftAux]
  | cons a xs ih =>
    simp only [List.cons_append, List.length_cons, leftAux, ih]
    rw [pow_succ, mul_assoc]

/-- Euclidean floor divisions compose for a nonnegative first divisor,
including on negative coefficients. -/
theorem quotient_leftAux (d e : ℤ) (xs : List ℤ) (hd : 0 ≤ d) :
    quotient e (leftAux d xs) = leftAux (d * e) xs := by
  induction xs generalizing d with
  | nil => rfl
  | cons a xs ih =>
    change (a / d / e) :: quotient e (leftAux (2 * d) xs) =
      (a / (d * e)) :: leftAux (2 * (d * e)) xs
    rw [Int.ediv_ediv_of_nonneg hd, ih (2 * d) (by omega), mul_assoc]

/-- Evaluate the normalized coefficients using the coordinate of each leaf.
The offset includes any additional outer power-of-two floor. -/
def shiftList (offset : ℕ) : Blocks → List ℤ
  | .empty => []
  | .leaf a => [a >>> offset]
  | .join lo hi => shiftList offset lo ++ shiftList (offset + lo.size) hi

theorem shiftList_eq_leftAux (offset : ℕ) (w : Blocks) :
    shiftList offset w = leftAux ((2 : ℤ) ^ offset) w.list := by
  induction w generalizing offset with
  | empty => rfl
  | leaf a =>
    simp only [shiftList, Blocks.list, leftAux, Int.shiftRight_eq_div_pow,
      Int.natCast_pow, Nat.cast_ofNat]
  | join lo hi ihLo ihHi =>
    simp only [shiftList, Blocks.list, leftAux_append, Blocks.size_eq, ihLo, ihHi, pow_add]
    rw [mul_comm ((2 : ℤ) ^ offset) ((2 : ℤ) ^ lo.list.length)]

/-- Normalization with the original absolute-tail truncation. -/
def normalized (m k : ℕ) (p : Blocks) : List ℤ :=
  truncate m (shiftList k p)

theorem normalized_eq (m k : ℕ) (p : Blocks) :
    normalized m k p = truncate m (quotient ((2 : ℤ) ^ k) (leftAux 1 p.list)) := by
  rw [normalized, shiftList_eq_leftAux,
    quotient_leftAux 1 ((2 : ℤ) ^ k) p.list (by decide), one_mul]

/-- Pass the faster computation to the unchanged production theorem. -/
theorem branch_left_normalized_shift {p c : Blocks} {t : ℚ} {k m : ℕ}
    (hn : normalized m k p = c.list)
    (hc : Covers (2 * t - ((0 : ℤ) : ℚ)) c) : Branch 0 t p :=
  branch_left_normalized (c := c) (k := k) (m := m) (by simpa only [normalized_eq] using hn) hc

/-- Compare coefficient by coefficient, without comparing expressions for lists. -/
def check (m k : ℕ) (p c : Blocks) : Bool :=
  (normalized m k p).isEqv c.list (· == ·)

theorem normalized_of_check {p c : Blocks} {m k : ℕ}
    (h : check m k p c = true) : normalized m k p = c.list := by
  simpa [check, List.isEqv_eq] using h

theorem branch_left_normalized_check {p c : Blocks} {t : ℚ} {k m : ℕ}
    (h : check m k p c = true)
    (hc : Covers (2 * t - ((0 : ℤ) : ℚ)) c) : Branch 0 t p :=
  branch_left_normalized_shift (normalized_of_check h) hc

end NextProof.Compact.LeftKernel
