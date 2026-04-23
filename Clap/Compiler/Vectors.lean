import Clap.Compiler.Wheels

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
  let arraySize ← mkAppM ``Array.size #[array]
  mkAppM ``Vector.mk #[array, ←mkEqRefl arraySize]

def needsExploding (e : Expr) : SimpM Bool := do
  let t ← inferType e
  return t.isAppOf ``Vector

simproc_decl explodeVectorProc (_) := fun e ↦ do
  let t ← inferType e
  let_expr Vector t sz := t | return .continue
  
  if e.isFVar && (←needsExploding e)
  then trace[Clap.Compile.simp.kaboom]
         m!"Exploding: {e}\n--->\n{←sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!}"
       logInfo m!"Exploding: {e}\n--->\n{←sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!}"
       return .done ⟨←sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!, .none, true⟩
  else return .continue

simproc_decl dontExplodeVector (GetElem.getElem _ _ _) := fun e ↦ do
  let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | unreachable!
  let_expr Vector _ _ := ← inferType coll | return .continue
  return .done ⟨e, .none, true⟩

simproc_decl dontExplodeVector! (GetElem?.getElem! _ _) := fun e ↦ do
  let_expr GetElem?.getElem! _ _ _ _ _ _ coll _ := e | unreachable!
  let_expr Vector _ _ := ← inferType coll | return .continue
  return .done ⟨e, .none, true⟩

-- attribute [simproc] explodeVectorProc
-- attribute [simproc↓] dontExplodeVector
-- attribute [simproc↓] dontExplodeVector!

end Clap.Compiler
