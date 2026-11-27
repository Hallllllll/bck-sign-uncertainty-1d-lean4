import NextProof.TailPacked
import Lean

namespace NextProof.Compact.ArithmeticIO
open Lean Elab Term

-- A divided read avoids quadratic work on multi-kilobyte signed integers.
private partial def readNat (data : ByteArray) (start n : Nat) : Nat := Id.run do
  if n ≤ 7 then
    let mut value := 0
    for i in [0:n] do
      value := (value <<< 8) + data[start+n-1-i]!.toNat
    return value
  let m := n/2
  return (readNat data (start+m) (n-m) <<< (8*m)) + readNat data start m

private partial def balanced (xs : Array Expr) (start n : Nat) : Expr := Id.run do
  if n = 0 then return mkConst ``NextProof.Tail.Blocks.empty
  if n = 1 then return mkApp (mkConst ``NextProof.Tail.Blocks.leaf) xs[start]!
  let m := n/2
  return mkApp2 (mkConst ``NextProof.Tail.Blocks.join)
    (balanced xs start m) (balanced xs (start+m) (n-m))

/-- Read signed little-endian records into kernel literals. Paths are relative to
the source using the notation. Every coefficient is retained in the .olean. -/
elab "arithBlock% " path:str : term => do
  let base := (System.FilePath.mk (← getFileName)).parent.getD "."
  let bytes ← IO.FS.readBinFile (base / path.getString)
  let mut i := 0
  let mut xs := #[]
  while i < bytes.size do
    if i + 4 > bytes.size then throwError "truncated length"
    let n := readNat bytes i 4
    i := i+4
    if n == 0 || i+n > bytes.size then throwError "invalid record size"
    let v := readNat bytes i n
    let term := if bytes[i+n-1]! < 128 then
      mkApp (mkConst ``Int.ofNat) (mkRawNatLit v)
    else mkApp (mkConst ``Int.negSucc) (mkRawNatLit ((1 <<< (8*n))-v-1))
    xs := xs.push term
    i := i+n
  return balanced xs 0 xs.size

end NextProof.Compact.ArithmeticIO
