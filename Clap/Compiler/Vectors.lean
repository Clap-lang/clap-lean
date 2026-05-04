import Clap.Compiler.Wheels
import Qq
import Mathlib.Tactic

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

def inferVectorProof (vectorSansProof : Expr) : TermElabM Expr := do
  let .forallE _ argT _ _ ← inferType vectorSansProof | unreachable!
  let proof ← Term.mkTacticMVar argT (←`(by simp)) .term
  Term.synthesizeSyntheticMVarsNoPostponing
  pure (Expr.app vectorSansProof proof) >>= instantiateMVars

def mkVecLit (l : Expr) (sz : Expr) : TermElabM Expr := do
  -- logInfo m!"mkVecLit:\n{l}\nsz:\n{sz}"
  let array ← mkAppM ``List.toArray #[l]
  let t := (←inferType array).getAppArgs[0]!
  let u ← getDecLevel t
  let vectorSansProof := mkAppN (.const ``_root_.Vector.mk [u]) #[t, sz, array]
  inferVectorProof vectorSansProof

def sequenceAsVecExpr (name : Expr) (t : Expr) (len : Nat) : TermElabM Expr := do
  let array ← mkAppM ``List.toArray #[
    ←mkListLit t (←List.range len |>.mapM (getElemVectorOfIdx name))
  ]
  let u ← getDecLevel t
  inferVectorProof (mkAppN (.const ``Vector.mk [u]) #[t, toExpr len, array])

def needsExploding (e : Expr) : SimpM Bool := do
  let t ← inferType e
  return t.isAppOf ``Vector



/--
Intended as `↑` in combination with `↓dontExplodeVector`.

- `vec : Vector α k ==> #v[vec[0], vec[1], ..., vec[k - 1]]`
-/
dsimproc_decl explodeVector (_) := fun e ↦ do
  let t ← inferType e
  let_expr Vector t sz := t | return .continue
  
  if e.isFVar && (←needsExploding e)
  then match (←Simp.simp sz).1.nat? with
       | .none => logError m!"{(←Simp.simp sz).1} is not ground"
                  return .done e
       | .some n => let explodedVec ← (sequenceAsVecExpr e t n).run'
                    trace[Clap.Compile.simp.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
                    return .done explodedVec
  else return .continue

def rejectVectorSansProof (coll e : Expr) : SimpM Simp.DStep := do
  let_expr Vector _ _ := ← inferType coll | return .continue
  return .done e

/--
Use with `↓`.
-/
dsimproc_decl dontExplodeVector (GetElem.getElem _ _ _) := fun e ↦ do
  let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | unreachable!
  if coll.isFVar
  then
    rejectVectorSansProof coll e
  else 
    return .continue
  
end Clap.Compiler
