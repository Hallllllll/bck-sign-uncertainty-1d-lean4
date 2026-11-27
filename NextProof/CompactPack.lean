import NextProof.TailPacked
import Init.Data.List.Sort.Lemmas

namespace NextProof.Tail.Blocks

/-- Split at a power of two using arithmetic shifts on the signed integer. -/
def centeredSplit (bits : ℕ) (z : ℤ) : ℤ × ℤ :=
  let half := ((1 : ℤ) <<< bits) >>> 1
  let high := (z + half) >>> bits
  (z - (high <<< bits), high)

theorem centeredSplit_eq (bits : ℕ) (z : ℤ) :
    let q : ℤ := 2 ^ bits
    centeredSplit bits z = ((z + q / 2) % q - q / 2, (z + q / 2) / q) := by
  simp only [centeredSplit, Int.shiftLeft_eq, Int.shiftRight_eq_div_pow, one_mul, pow_one,
    Int.natCast_pow, Nat.cast_ofNat, Prod.mk.injEq, and_true]
  have h := Int.emod_add_ediv_mul (z + (2 : ℤ) ^ bits / 2) (2 ^ bits)
  omega

/-- Decode a packed integer into the supplied shape, with the low coefficients
first. Empty subtrees consume no digits. The final leaf can hold any integer. -/
def decode (stride : ℕ) (shape : Blocks) (z : ℤ) : Blocks :=
  match shape with
  | .empty => .empty
  | .leaf _ => .leaf z
  | .join lo hi =>
    if lo.size = 0 then
      .join (lo.decode stride 0) (hi.decode stride z)
    else if hi.size = 0 then
      .join (lo.decode stride z) (hi.decode stride 0)
    else
      let parts := centeredSplit (stride * lo.size) z
      .join (lo.decode stride parts.1) (hi.decode stride parts.2)

@[simp] theorem decode_size (stride : ℕ) (shape : Blocks) (z : ℤ) :
    (shape.decode stride z).size = shape.size := by
  induction shape generalizing z with
  | empty => rfl
  | leaf _ => rfl
  | join lo hi ihLo ihHi =>
    simp only [decode]
    split
    · simp [Blocks.size, ihLo, ihHi]
    · split <;> simp [Blocks.size, ihLo, ihHi]

@[simp] theorem decode_length (stride : ℕ) (shape : Blocks) (z : ℤ) :
    (shape.decode stride z).list.length = shape.list.length := by
  simp only [← Blocks.size_eq, decode_size]

/-- Reconstruction holds at the packing radix for every shape of positive size. -/
theorem decode_subst (stride : ℕ) (shape : Blocks) (z : ℤ) (h : shape.size ≠ 0) :
    (shape.decode stride z).subst (2 ^ stride : ℤ) = z := by
  suffices he : (shape.decode stride z).subst (2 ^ stride : ℤ) =
      if shape.size = 0 then 0 else z by simpa [h] using he
  clear h
  induction shape generalizing z with
  | empty => rfl
  | leaf _ => simp [decode, Blocks.size, Blocks.subst]
  | join lo hi ihLo ihHi =>
    by_cases hlo : lo.size = 0
    · simp [decode, Blocks.subst, Blocks.size, hlo, ihLo, ihHi]
    · by_cases hhi : hi.size = 0
      · simp [decode, Blocks.subst, Blocks.size, hlo, hhi, ihLo, ihHi]
      · have hsum : lo.size + hi.size ≠ 0 := by omega
        simp only [decode, hlo, hhi, ite_false, centeredSplit_eq, Blocks.subst, decode_size, ihLo, ihHi,
          Blocks.size, hsum, ← pow_mul]
        let q : ℤ := 2 ^ (stride * lo.size)
        change (z + q / 2) % q - q / 2 + q * ((z + q / 2) / q) = z
        calc
          _ = ((z + q / 2) % q + (z + q / 2) / q * q) - q / 2 := by ring
          _ = z := by rw [Int.emod_add_ediv_mul]; ring

/-- Build a near-equal-halves tree in ascending coefficient order. -/
def ofListBalanced (xs : List ℤ) : Blocks :=
  match xs with
  | [] => .empty
  | [x] => .leaf x
  | a :: b :: rest =>
    let halves := List.MergeSort.Internal.splitInTwo ⟨a :: b :: rest, rfl⟩
    .join (ofListBalanced halves.1.val) (ofListBalanced halves.2.val)
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd, List.length_take, List.length_drop,
      List.length_cons]
    omega

@[simp] theorem ofListBalanced_list (xs : List ℤ) : (ofListBalanced xs).list = xs := by
  fun_induction ofListBalanced with
  | case1 => rfl
  | case2 => rfl
  | case3 a b rest halves ihLo ihHi =>
    simp only [Blocks.list, ihLo, ihHi]
    exact List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd _

@[simp] theorem ofListBalanced_size (xs : List ℤ) : (ofListBalanced xs).size = xs.length := by
  rw [Blocks.size_eq, ofListBalanced_list]

end NextProof.Tail.Blocks
