import Lean
import Qq
import Mathlib.Tactic
import Mathlib.Lean.Meta
import Clap.Spec
import Clap.Lang

open Lean Qq Meta

namespace Clap

def isNameFormer (e : Expr) (typeName : Name) : MetaM Bool :=
  forallTelescopeReducing e fun _ ret ↦ return ret.isAppOf typeName

def isPrivileged (e : Expr) : MetaM Bool := do
  return (←Meta.isTypeFormer e) || /-Probably wrong.-/ e.isAppOf ``Bind.bind ||
         (←Meta.inferType e).isAppOf ``Monad || (←Meta.inferType e).isAppOf ``Bind ||
         (←isNameFormer (←Meta.inferType e) ``Bind) || (←isNameFormer (←Meta.inferType e) ``Monad)
        -- || (←isNameFormer (←Meta.inferType e) ``Lang.Core)

/--
TODO: Temporary. We'll want to reduce this at some point.
-/
def isArith (e : Expr) : MetaM Bool := do
  return [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HPow.hPow, ``OfNat.ofNat].map e.isAppOf |>.any (·==true)

def _root_.Lean.Expr.isIrreducibleExpr (e : Expr) : MetaM Bool := do
  e.getAppFn.constName?.elim (return false) isIrreducible

def unfoldAnyStep (e : Expr) : MetaM TransformStep := do
  if ←isArith e then return .continue
  if (←isInstance e.getAppFn.constName) then return .continue
  if (←e.isIrreducibleExpr) || (←isPrivileged e) then return .continue
  match ← reduceMatcher? e with
  | .reduced v =>
         return .done v -- return .visit v
  | _ => let_expr Array.get!Internal _ _ arr idx := e |
           let some v ← unfoldDefinition? e | return .continue
           return .done v -- return .visit v
         -- TODO: Special casing arrays here is temporary.
         return .done (←mkAppM ``List.get!Internal #[←mkAppM ``Array.toList #[arr], idx])


def unfoldAny (e : Expr) : MetaM Expr := do
  Meta.transform e (skipConstInApp := true) (pre := unfoldAnyStep)

def unfold_mAny (m : Nat) (verbose : Bool := false) (e : Expr) : MetaM Expr := do
  if verbose then
    logInfo m!"Unfold_mAny:\n{e}}"
  let mut res := e
  for i in List.range m do
    if verbose then
      logInfo m!"res[{i}]:\n{res}\n"
    let res' ← unfoldAny res
    if res' == res then
      if verbose then
        logInfo m!"Loop detected [{i}]:\n{res}"
      return res'
    res := res'
  logInfo m!"Limit reached [{m}]:\n{res}"
  return res

/--
TODO: Unused.
-/
def forceFoldProjs (e : Expr) : MetaM Expr := do
  if (e.find? (·.isProj)).isNone then return e
  let post (e : Expr) := do
    if ←isPrivileged e then return .continue
    let .proj structName idx s := e | return .done e
    let some info := getStructureInfo? (←getEnv) structName | return .done e
    if h : idx < info.fieldNames.size then
      let fieldName := info.fieldNames[idx]
      return .visit (← withDefault <| mkProjection s fieldName)
    else
      return .done e
  Meta.transform e (post := post)

def foldProjs (e : Expr) : MetaM Expr := do
  if (e.find? (·.isProj)).isNone then return e
  let post (e : Expr) := do
    let .some e' ← reduceProj? e | return .continue
    return .visit e'
  Meta.transform e (post := post)

def zetaHaveStep (e : Expr) : MetaM TransformStep := do
  let .letE _ _ v b _ := e | return .continue
  return .visit <| Meta.expandLet b #[v]

def zetaHave (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := zetaHaveStep)

/--
TODO: Think about the ordering here. Do we need unfold / zeta / unfold, do we repeat, etc.
-/
def reduceExpr (e : Expr) : MetaM Expr :=
  let numIters := 128
  do pure e >>=
     unfold_mAny numIters false >>= (Core.betaReduce ·) >>=
     zetaHave >>=
     unfold_mAny numIters false >>= (Core.betaReduce ·) >>=
     foldProjs                  >>= (Core.betaReduce ·) >>=
     unfold_mAny numIters false >>= (Core.betaReduce ·)

open MVarId in
def _root_.Lean.MVarId.reduceTarget (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget (f := reduceExpr)

open Elab Tactic in
elab "test_reduce" : tactic => do
  liftMetaTactic' MVarId.reduceTarget

end Clap
