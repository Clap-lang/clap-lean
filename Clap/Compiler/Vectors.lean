import Lean

import Clap.Compiler.Simp

open Lean Meta Elab

namespace Clap.Compiler

def sequenceAsVecExpr (name : Expr) (t : Expr) (len : Nat) : MetaM Expr := do
  let array ← mkAppM ``Array.mk #[
    ←mkListLit t (←List.range len |>.mapM fun i ↦ do mkAppM ``GetElem?.getElem! #[
      name,
      Expr.lit (.natVal i)
    ])
  ]
  let vecSansProof := mkAppN (.const ``Vector.mk [.zero]) #[t, toExpr len, array]
  return Expr.app vecSansProof (←mkAppM ``Eq.refl #[←mkAppM ``Array.size #[array]])

def collectionTypeAndSize (e : Expr) : TermElabM (Expr × Expr) := do
  let_expr Vector t n := ←inferType e | throwError m!"Not a collection:\n{e}"
  return (t, ←Simp.simplify {} n)

def needsExploding (e : Expr) : TermElabM Bool := do
  let t ← inferType e
  return t.isAppOf ``Vector

def explodeSequences (e : Expr) : TermElabM Expr := do
  Meta.transform (skipConstInApp := true) e fun e ↦ do
    if e.isBVar && (←needsExploding e)
    then let (t, sz) ← collectionTypeAndSize e
         return .done <| ←sequenceAsVecExpr e t sz.nat?.get!
    else return .continue

def lambdaWithExpandedVecs (e : Expr) : TermElabM Expr :=
  lambdaTelescope e fun args body ↦ do
    let body ← explodeSequences body
    mkLambdaFVars args body

end Clap.Compiler
