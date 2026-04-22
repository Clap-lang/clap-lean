import Lean

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

-- def collectionTypeAndSize (e : Expr) : SimpM (Expr × Expr) := do
--   let_expr Vector t n := ←inferType e | throwError m!"Not a collection:\n{e}"
--   return (t, (←Simp.simp n).expr) -- TODO: This is probably too 'strong'.

def needsExploding (e : Expr) : SimpM Bool := do
  let t ← inferType e
  return t.isAppOf ``Vector

-- def explodeSequences (e : Expr) : SimpM Expr := do
--   Meta.transform (skipConstInApp := true) e fun e ↦ do
--     if e.isBVar && (←needsExploding e)
--     then let (t, sz) ← collectionTypeAndSize e
--          return .done <| ←sequenceAsVecExpr e t sz.nat?.get!
--     else return .continue

-- def lambdaWithExpandedVecs (e : Expr) : SimpM Expr :=
--   lambdaTelescope e fun args body ↦ do
--     let body ← explodeSequences body
--     mkLambdaFVars args body

-- TODO: Cannot work yet. We'll need a `GetElem.getElem` prevention.
simproc_decl explodeVectorProc (_) := fun e ↦ do
  let t ← inferType e
  let_expr Vector t sz := t | return .continue
  
  if e.isBVar && (←needsExploding e)
  then -- let (t, sz) ← collectionTypeAndSize e
       logWarning m!"Exploding: {e}\n--->\n{←sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!}"
       return .done ⟨←sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!, .none, true⟩
       -- TODO: Probably too strong to simp here.
  else return .continue

-- attribute [simproc] explodeVectorProc

end Clap.Compiler
