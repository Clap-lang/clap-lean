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
  -- Do we want to catch irreducible expressions?
  if (←isInstance e.getAppFn.constName) then return .continue
  if (←e.isIrreducibleExpr) || (←isPrivileged e) then return .continue
  match ← reduceMatcher? e with
  | .reduced v => return .visit v
  | _ => let some v ← unfoldDefinition? e | return .continue
         return .visit v

def unfoldAny (e : Expr) : MetaM Expr := do
  Meta.transform e (skipConstInApp := true) (pre := unfoldAnyStep)

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

def zetaHaveStepPre (p e : Expr) : MetaM TransformStep := do
  let .letE _ _ v b _ := e | return .continue

  let blacklist :=
    Expr.const (us := []) <$> [
      ``Spec.Compiler.is_zero,
      ``Spec.Compiler.num2bits,
      ``Spec.Compiler.share
    ]

  if ←blacklist.anyM fun rejE ↦ do
    isDefEq v.getAppFn rejE then
      logInfo m!"Rejected. Continuation: {b}"
      return .continue b

  return .visit <| b.instantiate1 v

def zetaHave (p e : Expr) : MetaM Expr := do
  logInfo m!"{e}"
  Meta.transform e (pre := zetaHaveStepPre p)

partial def zeta (e : Expr) : MetaM Expr := do
  match e with
  | .letE declName type value body nondep =>
    -- TODO: Checking defeq is tricky, the expressions can contain bvars :thinking:.
    if blacklist.contains value.getAppFn.constName then
      return .letE declName type (←zeta value) (←zeta body) nondep
    zeta (body.instantiate1 value)
  | .app fn arg => return .app (← zeta fn) (← zeta arg)
  | .lam binderName binderType body binderInfo =>
    return .lam binderName binderType (←zeta body) binderInfo
  | .forallE binderName binderType body binderInfo =>
    return .forallE binderName binderType (←zeta body) binderInfo
  | _ => return e
  where blacklist := [
    ``Spec.Compiler.is_zero,
    ``Spec.Compiler.num2bits,
    ``Spec.Compiler.share]

/--
TODO: Think about the ordering here. Do we need unfold / zeta / unfold, do we repeat, etc.
-/
def reduceExpr (p e : Expr) : MetaM Expr :=
  pure e >>=
  unfoldAny  >>= (Core.betaReduce ·) >>=
  zeta >>=
  unfoldAny  >>= (Core.betaReduce ·) >>=
  foldProjs  >>= (Core.betaReduce ·)

open MVarId in
def _root_.Lean.MVarId.reduceTarget (p : Expr) (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget (f := reduceExpr p)

open Elab Tactic in
elab "test_reduce" "using" p:ident : tactic => do
  liftMetaTactic' (MVarId.reduceTarget (Expr.const p.getId []))

end Clap
