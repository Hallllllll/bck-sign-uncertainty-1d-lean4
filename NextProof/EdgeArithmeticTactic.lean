import NextProof.EdgeArithmetic
import Lean

namespace NextProof.Compact.EdgeArithmetic
open NextProof.Tail
open Lean Meta Elab Tactic

private theorem homJoin (s x : ℤ) (a b : Blocks) (m n : ℕ) (u v w : ℤ)
    (ha : fastHom s x a = u) (hb : fastHom s x b = v)
    (hm : a.size = m) (hn : b.size = n) (h : 2^n*u+(x+s)^m*v=w) :
    fastHom s x (.join a b) = w := by simp only [fastHom, ha, hb, hm, hn, h]

private theorem substJoin (x : ℤ) (a b : Blocks) (m : ℕ) (u v w : ℤ)
    (ha : a.subst x=u) (hb : b.subst x=v) (hm : a.size=m) (h : u+x^m*v=w) :
    (Blocks.join a b).subst x=w := by simp only [Blocks.subst, ha, hb, hm, h]

private theorem finish (s x k : ℤ) (p c e : Blocks) (u v w : ℤ)
    (hp : fastHom s x p=u) (hc : c.subst x=v) (he : e.subst x=w)
    (h : u=k*v+w) : fastHom s x p=k*c.subst x+e.subst x := by rw [hp,hc,he,h]

private def intExpr : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

private def intValue (term : Expr) : MetaM Int := do
  let e ← whnf term
  let some n := (← whnf e.appArg!).rawNatLit? | throwError "expected integer literal"
  if e.isAppOf ``Int.ofNat then return .ofNat n
  if e.isAppOf ``Int.negSucc then return .negSucc n
  throwError "expected integer constructor"

private partial def readBlock (term : Expr) : MetaM Blocks := do
  let e ← whnf term
  if e.isConstOf ``Blocks.empty then return .empty
  if e.isAppOf ``Blocks.leaf then return .leaf (← intValue e.appArg!)
  if e.isAppOf ``Blocks.join then
    return .join (← readBlock e.appFn!.appArg!) (← readBlock e.appArg!)
  throwError "expected concrete Blocks"

private structure Val where
  size : Nat
  value : Int
  proof : Expr

private def checked (type value : Expr) : MetaM Expr := do
  return mkConst (← mkAuxLemma [] type value (kind? := some `_edgeCheckpoint) (cache := false))

/-- Each checked declaration resets the kernel's reduction cache. Values predicted by
the elaborator are only witnesses for definitional equalities checked in that kernel. -/
private partial def certify (hom : Bool) (s x : Int) (se xe tree : Expr)
    (depth : Nat) : MetaM Val := do
  let lhs := if hom then mkApp3 (mkConst ``fastHom) se xe tree
    else mkApp2 (mkConst ``Blocks.subst) xe tree
  let t ← whnf tree
  if depth == 0 || !t.isAppOf ``Blocks.join then
    let b ← readBlock tree
    let v := if hom then fastHom s x b else b.subst x
    let lit := intExpr v
    return ⟨b.size, v, ← checked (← mkEq lhs lit) (← mkEqRefl lit)⟩
  let a := t.appFn!.appArg!
  let b := t.appArg!
  let lo ← certify hom s x se xe a (depth-1)
  let hi ← certify hom s x se xe b (depth-1)
  let v := if hom then 2^hi.size * lo.value + (x+s)^lo.size * hi.value
    else lo.value + x^lo.size * hi.value
  let lit := intExpr v
  let m := mkRawNatLit lo.size
  let n := mkRawNatLit hi.size
  let u₁ := intExpr lo.value
  let u₂ := intExpr hi.value
  let h ← mkEqRefl lit
  let hm ← mkEqRefl m
  let hn ← mkEqRefl n
  let proof := if hom then
      mkAppN (mkConst ``homJoin) #[se,xe,a,b,m,n,u₁,u₂,lit,lo.proof,hi.proof,hm,hn,h]
    else
      mkAppN (mkConst ``substJoin) #[xe,a,b,m,u₁,u₂,lit,lo.proof,hi.proof,hm,h]
  return ⟨lo.size+hi.size,v, ← checked (← mkEq lhs lit) proof⟩

/-- Prove a closed edge sample using kernel-checked subtree checkpoints. The
argument specifies the number of balanced tree levels to split before reduction. -/
elab "edge_arith_checkpoint " depth:num : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_,lhs,rhs) := target.eq? | throwError "expected an edge scalar equality"
  unless lhs.isAppOfArity ``fastHom 3 do throwError "expected fastHom on the left"
  let #[se,xe,p] := lhs.getAppArgs | throwError "invalid fastHom"
  unless rhs.isAppOf ``HAdd.hAdd do throwError "expected a scaled child plus residual"
  let mul := rhs.appFn!.appArg!
  unless mul.isAppOf ``HMul.hMul do throwError "expected a scaled child"
  let k := mul.appFn!.appArg!
  let child := mul.appArg!
  let residual := rhs.appArg!
  unless child.isAppOf ``Blocks.subst && residual.isAppOf ``Blocks.subst do
    throwError "expected Blocks.subst on the right"
  let c := child.appArg!
  let e := residual.appArg!
  let s ← intValue se
  let x ← intValue xe
  let a ← certify true s x se xe p depth.getNat
  let b ← certify false s x se xe c depth.getNat
  let d ← certify false s x se xe e depth.getNat
  unless a.value == (← intValue k)*b.value + d.value do throwError "edge scalar mismatch"
  let h := mkAppN (mkConst ``finish) #[se,xe,k,p,c,e,intExpr a.value,intExpr b.value,
    intExpr d.value,a.proof,b.proof,d.proof,← mkEqRefl (intExpr a.value)]
  goal.assign h

end NextProof.Compact.EdgeArithmetic
