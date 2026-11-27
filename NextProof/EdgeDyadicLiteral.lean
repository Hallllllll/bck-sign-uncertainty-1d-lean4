import NextProof.EdgeDyadic
import Lean

namespace NextProof.EdgeRecovery.Literal
open Lean Meta Elab Term NextProof.Tail

private def integer (e : Expr) : MetaM Int := do
  let e ← whnf e
  unless e.isAppOf ``Int.ofNat || e.isAppOf ``Int.negSucc do
    throwError "expected a signed integer constructor"
  let some n := (← whnf e.appArg!).rawNatLit? | throwError "expected a raw natural literal"
  return if e.isAppOf ``Int.ofNat then .ofNat n else .negSucc n

private partial def block (e : Expr) : MetaM Blocks := do
  let e ← whnf e
  if e.isConstOf ``Blocks.empty then return .empty
  if e.isAppOf ``Blocks.leaf then return .leaf (← integer e.appArg!)
  if e.isAppOf ``Blocks.join then return .join (← block e.appFn!.appArg!) (← block e.appArg!)
  throwError "expected a closed Blocks tree"

private def raw : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

/-- Produce a candidate integer. Each use is paired with a separate kernel
equality in a concrete Part; this elaborator contributes no proof. -/
elab "dyadicValue% " mode:str b:num d:num p:term : term => do
  let e ← elabTerm p (some (mkConst ``Blocks))
  let t ← withTransparency .all (block e)
  let k ← match mode.getString with
    | "parent" => pure Kind.parent
    | "plain" => pure Kind.plain
    | _ => throwError "unknown dyadic evaluation kind"
  return raw (ground k b.getNat d.getNat t)

end NextProof.EdgeRecovery.Literal
