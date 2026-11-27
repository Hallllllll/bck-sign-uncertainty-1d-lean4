import Lean
import NextProof.TailPacked

/-! This elaborator imports signed coefficient records as ordinary kernel literals.
The algebraic identities accompanying those literals are checked separately. -/
namespace NextProof.Compact.Input
open Lean Elab Term

private partial def unsignedLE (b : ByteArray) (start length : Nat) : Nat := Id.run do
  if length ≤ 8 then
    let mut v := 0
    for j in [0:length] do
      v := (v <<< 8) + b[start+length-1-j]!.toNat
    return v
  let k := length/2
  return unsignedLE b start k + (unsignedLE b (start+k) (length-k) <<< (8*k))

private partial def assemble (a : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo then mkConst ``NextProof.Tail.Blocks.empty
  else if hi = lo+1 then mkApp (mkConst ``NextProof.Tail.Blocks.leaf) a[lo]!
  else
    let mid := (lo+hi)/2
    mkApp2 (mkConst ``NextProof.Tail.Blocks.join) (assemble a lo mid) (assemble a mid hi)

elab "edgeBlocks% " path:str : term => do
  let parent := (System.FilePath.mk (← getFileName)).parent.getD "."
  let p := parent / ".." / "compact_cert" / path.getString
  let b ← IO.FS.readBinFile p
  let mut i := 0
  let mut entries := #[]
  while i < b.size do
    if i+4 > b.size then throwError "truncated integer length in {p}"
    let n := unsignedLE b i 4
    i := i+4
    if n=0 || i+n>b.size then throwError "invalid signed integer length in {p}"
    let v := unsignedLE b i n
    let term := if b[i+n-1]!.toNat < 128 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit v)
      else mkApp (mkConst ``Int.negSucc) (mkRawNatLit ((1 <<< (8*n))-v-1))
    entries := entries.push term
    i := i+n
  return assemble entries 0 entries.size

end NextProof.Compact.Input
