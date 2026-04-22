import Clap.Compiler.Wheels
import Qq

import Lean

open Lean Meta Elab Qq

namespace Clap.Compiler

def getElemVectorOfIdx (coll : Expr) (idx : Nat) : TermElabM Expr := do
  let_expr Vector _ sz := ← Meta.inferType coll | throwError m!"{coll} must be a Vector."
  let idxQ : Q(Nat) := ToExpr.toExpr idx
  let szQ : Q(Nat) := sz
  let getElemSansProof ← Meta.mkAppM ``GetElem.getElem #[coll, ToExpr.toExpr idx]
  let proof ← Elab.Term.mkTacticMVar q($idxQ < $szQ) (←`(by get_elem_tactic)) .term
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars <| mkAppN getElemSansProof #[proof]

def sequenceAsVecExpr (name : Expr) (t : Expr) (len : Nat) : TermElabM Expr := do
  let array ← mkAppM ``Array.mk #[
    ←mkListLit t (←List.range len |>.mapM (getElemVectorOfIdx name))
  ]
  let vectorSansProof := mkAppN (.const ``Vector.mk [0]) #[t, toExpr len, array]
  let .forallE _ argT _ _ ← inferType vectorSansProof | unreachable!
  let proof ← Term.mkTacticMVar argT (←`(by simp)) .term
  Term.synthesizeSyntheticMVarsNoPostponing
  pure (Expr.app vectorSansProof proof) >>= instantiateMVars

def needsExploding (e : Expr) : SimpM Bool := do
  let t ← inferType e
  return t.isAppOf ``Vector

dsimproc_decl explodeVectorProc (_) := fun e ↦ do
  let t ← inferType e
  let_expr Vector t sz := t | return .continue
  
  if e.isFVar && (←needsExploding e)
  then trace[Clap.Compile.simp.kaboom]
         m!"Exploding:\n{e}\n==>\n{←(sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!).run'}"
       return .done (←(sequenceAsVecExpr e t (←Simp.simp sz).1.nat?.get!).run')
  else return .continue

def rejectVectorSansProof (coll e : Expr) : SimpM Simp.DStep := do
  let_expr Vector _ _ := ← inferType coll | return .continue
  return .done e

dsimproc_decl dontExplodeVector (GetElem.getElem _ _ _) := fun e ↦ do
  let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | unreachable!
  if coll.isFVar
  then
    rejectVectorSansProof coll e
  else 
    return .continue

-- simproc_decl dontExplodeVector' (getElem _ _ _) := fun e ↦ do
--   let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | unreachable!
--   let_expr Vector.mk _ _ _ _ := coll | rejectVectorSansProof coll e
--   return .continue

-- simproc_decl dontExplodeVector! (GetElem?.getElem! _ _) := fun e ↦ do
--   let_expr GetElem?.getElem! _ _ _ _ _ _ coll _ := e | unreachable!
--   let_expr Vector.mk _ _ _ _ := coll | rejectVectorSansProof coll e
--   return .continue








-- simproc_decl getElemOverride (getElem (Vector.mk _ _) _ _) := fun e ↦ do
--   logInfo m!"HELLO"
--   let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | unreachable!
--   let_expr Vector _ _ := ← inferType coll | return .continue
--   return .visit ⟨e, .none, true⟩
  

-- attribute [simproc] explodeVectorProc
-- attribute [simproc↓] dontExplodeVector
-- attribute [simproc↓] dontExplodeVector'
-- attribute [simproc↓] dontExplodeVector!

-- example {v : Vector Nat 4} : v = #v[v[0], v[1], v[2], #v[1, 2][0]] := by
--   simp [explodeVectorProc, ↓dontExplodeVector]
--   sorry

  
end Clap.Compiler
