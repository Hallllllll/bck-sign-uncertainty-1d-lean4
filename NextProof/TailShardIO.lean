import Lean

/-! Binary literals for independently checked arithmetic certificates. Each record
has a four-byte unsigned length and a signed little-endian two's-complement value.
Elaboration produces ordinary kernel integer constructors with raw natural literals. -/

namespace NextProof.Tail.ShardIO
open Lean Elab Term

private partial def natLE (b : ByteArray) (i n : Nat) : Nat := Id.run do
  if n ≤ 8 then
    let mut a := 0
    for k in [0:n] do a := (a <<< 8) + b[i+n-1-k]!.toNat
    return a
  let m := n/2
  return natLE b i m + (natLE b (i+m) (n-m) <<< (8*m))

private def records (path : String) : TermElabM (Array Expr) := do
  let parent := (System.FilePath.mk (← getFileName)).parent.getD "."
  let b ← IO.FS.readBinFile (parent / ".." / "tail_cert" / "shards" / path)
  let mut result := #[]
  let mut i := 0
  while i < b.size do
    if i+4 > b.size then throwError "truncated shard record header"
    let n := natLE b i 4
    i := i+4
    if n == 0 || i+n > b.size then throwError "invalid shard record length"
    let value := natLE b i n
    let e := if b[i+n-1]! < 128 then mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit value)
      else mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit ((1 <<< (8*n)) - value - 1))
    result := result.push e
    i := i+n
  return result

elab "tailInts% " path:str : term => do
  let t := Lean.mkConst ``Int
  let xs ← records path.getString
  return xs.foldr (fun x tail => mkApp3 (Lean.mkConst ``List.cons [.zero]) t x tail)
    (mkApp (Lean.mkConst ``List.nil [.zero]) t)

elab "tailInt% " path:str : term => do
  let xs ← records path.getString
  if xs.size != 1 then throwError "expected a single scalar"
  return xs[0]!

end NextProof.Tail.ShardIO
