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
    -- TODO: Is this a hack?
    -- TODO: I don't think check is needed anymore.
    if e'.isAppOf ``id then return .continue
    return .visit e'
  Meta.transform e (post := post)

def zetaHaveStep (p e : Expr) : MetaM TransformStep := do
  let .letE _ _ v b _ := e | return .continue
  let blacklist :=
    (Expr.app (arg := p) ∘ Expr.const (us := [])) <$> [
      ``Spec.Compiler.is_zero,
      ``Spec.Compiler.num2bits,
      ``Spec.Compiler.share
    ]
  if ←blacklist.anyM fun e ↦ do
    isDefEq v.getAppFn e then
      return .continue

  return .visit <| Meta.expandLet b #[v]

def zetaHave (p e : Expr) : MetaM Expr := do
  Meta.transform e (pre := zetaHaveStep p)

/--
TODO: Think about the ordering here. Do we need unfold / zeta / unfold, do we repeat, etc.
-/
def reduceExpr (p e : Expr) : MetaM Expr :=
  pure e >>=
  unfoldAny  >>= (Core.betaReduce ·) >>=
  zetaHave p >>=
  unfoldAny  >>= (Core.betaReduce ·) >>=
  foldProjs  >>= (Core.betaReduce ·)

open MVarId in
def _root_.Lean.MVarId.reduceTarget (p : Expr) (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget (f := reduceExpr p)

open Elab Tactic in
elab "test_reduce" "using" p:ident : tactic => do
  liftMetaTactic' (MVarId.reduceTarget (Expr.const p.getId []))

end Clap
