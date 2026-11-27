import NextProof.TailKernel

namespace NextProof.Tail
open Polynomial

/-- A balanced sequence permits fast exact substitution in a large integer radix.
Leaf order is ascending exponent. -/
inductive Blocks
  | empty
  | leaf (a : ℤ)
  | join (lo hi : Blocks)
  deriving Inhabited

namespace Blocks

def list : Blocks → List ℤ
  | .empty => []
  | .leaf a => [a]
  | .join lo hi => lo.list ++ hi.list

def size : Blocks → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .join lo hi => lo.size+hi.size

theorem size_eq (a : Blocks) : a.size = a.list.length := by
  induction a <;> simp [size,list, *]

/-- Use the length of the low block, allowing shorter final blocks. -/
def subst (x : ℤ) : Blocks → ℤ
  | .empty => 0
  | .leaf a => a
  | .join lo hi => lo.subst x + x^lo.size * hi.subst x

def absBlocks : Blocks → Blocks
  | .empty => .empty
  | .leaf a => .leaf |a|
  | .join lo hi => .join lo.absBlocks hi.absBlocks

private theorem horner_append (x : ℤ) (a b : List ℤ) :
    horner x (a++b) = horner x a+x^a.length*horner x b := by
  induction a with
  | nil => simp [horner]
  | cons a as ih => simp only [List.cons_append, horner, ih, List.length_cons, pow_succ]; ring

theorem subst_eq (a : Blocks) (x : ℤ) : a.subst x = horner x a.list := by
  induction a with
  | empty => rfl
  | leaf w => simp [subst, list, horner]
  | join a b ha hb => simp [subst, list, horner_append, size_eq, ha, hb]

/-- Split a list into a tree of bounded height, preserving every coefficient even if
the requested balancing depth is too small. -/
def chain : List ℤ → Blocks
  | [] => .empty
  | a::as => .join (.leaf a) (chain as)

private theorem chain_list (xs : List ℤ) : (chain xs).list = xs := by
  induction xs <;> simp [chain, list, *]

def balanced : ℕ → List ℤ → Blocks
  | 0, xs => chain xs
  | d+1, xs =>
    if xs.length < 2 then chain xs
    else
      let k := xs.length/2
      .join (balanced d (xs.take k)) (balanced d (xs.drop k))

@[simp] theorem balanced_list (d : ℕ) (xs : List ℤ) : (balanced d xs).list = xs := by
  induction d generalizing xs with
  | zero => exact chain_list _
  | succ d ih => simp only [balanced]; split <;> simp [chain_list,list,ih]

private theorem abs_list (a : Blocks) : a.absBlocks.list = a.list.map abs := by
  induction a <;> simp [absBlocks,list, *]

theorem major_eq (a : Blocks) (x : ℤ) : a.absBlocks.subst x = major x a.list := by
  rw [subst_eq, abs_list]
  induction a.list with
  | nil => rfl
  | cons z l ih => simp only [List.map_cons,horner,major,Int.cast_id,ih]

/-- Packed integer identity certified with balanced arithmetic on both sides.
Evaluations and magnitude checks involve integers only. -/
theorem shift (a b : Blocks) (c B : ℤ) (hB : 0 < B)
    (hsize : a.absBlocks.subst (|c|+1) + b.absBlocks.subst 1 < B)
    (hval : a.subst (c+B) = b.subst B) :
    horner (C c+X) a.list = horner (X : ℤ[X]) b.list := by
  apply shift_eq hB
  · simpa only [major_eq] using hsize
  · simpa only [subst_eq] using hval

end Blocks
end NextProof.Tail
