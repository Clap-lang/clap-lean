import Lean
import Qq
import Clap.Spec
import Clap.Lang
import Clap.Compiler.Front.Wheels

open Lean Qq Meta

namespace Clap

def isNameFormer (e : Expr) (typeName : Name) : MetaM Bool :=
  forallTelescopeReducing e fun _ ret ↦ return ret.isAppOf typeName

def isBind (e : Expr) : MetaM Bool :=
  isDefEq e.getAppFn (.const ``Bind.bind [0, 0])

def getBindArgs! (e : Expr) : MetaM (Expr × Expr) := do
  let firstExplicitArg := (←getFunInfo e.getAppFn).paramInfo.findIdx (·.binderInfo.isExplicit)
  let args := e.getAppArgs
  return (args[firstExplicitArg]!, args[firstExplicitArg + 1]!)

def isStructuralBind (e : Expr) : MetaM Bool := do
  if !(←isBind e) then return false
  let (bindLhs, _) ← getBindArgs! e
  let some := Expr.const ``Option.some [0]
  let defeq ← isDefEq bindLhs.getAppFn some
  return defeq

open Meta in
def isVerboten (e : Expr) : MetaM Bool := do
  let eT ← inferType e
  return (←isTypeFormer e) ||
         eT.isAppOf ``Monad ||
         (←isBind e) ||
         (←isNameFormer eT ``Monad)

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
  if (←e.isIrreducibleExpr) || (←isVerboten e) then return .continue
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
def _forceFoldProjs (e : Expr) : MetaM Expr := do
  if (e.find? (·.isProj)).isNone then return e
  let post (e : Expr) := do
    if ←isVerboten e then return .continue
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

def _root_.Lean.Expr.isAppOfUptoDefEq (e₁ e₂ : Expr) : MetaM Bool := do
  let (mvars₁, _, _) ← forallMetaTelescope =<< inferType e₁
  let (mvars₂, _, _) ← forallMetaTelescope =<< inferType e₂
  isDefEq (mkAppN e₁ mvars₁) (mkAppN e₂ mvars₂)

partial def zeta (e : Expr) : MetaM Expr := do
  match e with
  | .letE declName type value body nondep =>
    if !value.isApp then zeta (body.instantiate1 value) else
    if ←blacklist.anyM value.getAppFn.isAppOfUptoDefEq then
      return Expr.letE declName type (←zeta value) (←zeta body) nondep
    zeta (body.instantiate1 value)
  | .app fn arg => return .app (← zeta fn) (← zeta arg)
  | .lam binderName binderType body binderInfo =>
    return .lam binderName binderType (←zeta body) binderInfo
  | .forallE binderName binderType body binderInfo =>
    return .forallE binderName binderType (←zeta body) binderInfo
  | _ => return e
  where blacklist := Expr.const (us := []) <$> [
    ``Spec.Compiler.isZero,
    ``Spec.Compiler.share]

def linearise (e : Expr) : MetaM Expr := do
  Meta.transform e fun e ↦ do
    let (``Bind.bind, ⟨_ :: _ :: _ :: _ :: lhs :: [rhs]⟩) := e.getAppFnArgs | return .continue
    let (``Bind.bind, ⟨_ :: _ :: lamArgT :: _ :: lhs' :: [rhs']⟩) := lhs.getAppFnArgs | return .continue
    let binderName ← getUnusedUserName `x
    withLocalDecl binderName .default lamArgT fun fvar ↦ do
      let lam ← mkLambdaFVars #[fvar] (←mkAppM ``Bind.bind #[.app rhs' fvar, rhs])
      return .visit (←Core.betaReduce (←mkAppM ``Bind.bind #[lhs', lam]))

lemma _root_.Option.some_bind {α β : Type} (x : α) (f : α → Option β) :
  Option.some x >>= f = f x := by simp

def letSome (e : Expr) : MetaM Expr := do
  Meta.transform (skipConstInApp := true) e fun e ↦ do
    if !(←isStructuralBind e) then return .continue
    let (lhs, rhs) ← getBindArgs! e
    /-
    We are being naughty. This is not definitionally equal, but we are pretending this is.
    It is perfectly fine for the compiler, but e.g. `test_reduce` now makes the kernel unhappy.

    `_proof` is why these things are equal and `_realTerm` is a term with which
    the kernel would be happy. Nevertheless, we ignore this for the time being.
    -/
    let _proof ← mkAppM ``Option.some_bind #[lhs.getAppArgs[1]!, rhs]
    let _realTerm := ←e.rewrite _proof

    return .visit (←Core.betaReduce (.app rhs (lhs.getAppArgs[1]!)))

/--
TODO: Think about the ordering here. Do we need unfold / zeta / unfold, do we repeat, etc.
-/
def reduceExpr' (e : Expr) : MetaM Expr :=
  let numIters := 128
  do pure e >>=
     unfold_mAny numIters false >>= (Core.betaReduce ·) >>=
     zeta >>=
     unfold_mAny numIters false >>= (Core.betaReduce ·) >>= linearise >>=
     foldProjs                  >>= (Core.betaReduce ·) >>=
     unfold_mAny numIters false >>= (Core.betaReduce ·) >>= letSome

def reduceStep (e : Expr) : MetaM Expr := do
  let cfg : Simp.Config := default
  let ctx ← mkSimpContext (simpOnly := true) (cfg := {cfg with zeta := false})
  let dsimp := fun e ↦ (·.1) <$> dsimp e ctx

  let unfoldAnyS ← unfoldAny e
  trace[Clap.Compiler.reduce.unfoldAny] m!"[unfoldAny]:\n{skipIdentity e unfoldAnyS}"

  let dsimpS ← dsimp unfoldAnyS
  trace[Clap.Compiler.reduce.dsimp] m!"[dsimp]:\n{skipIdentity unfoldAnyS dsimpS}"

  let betaS ← Core.betaReduce dsimpS
  trace[Clap.Compiler.reduce.beta] m!"[beta]:\n{skipIdentity dsimpS betaS}"

  let zetaS ← zeta betaS
  trace[Clap.Compiler.reduce.zeta] m!"[zeta]:\n{skipIdentity betaS zetaS}"

  let lineariseS ← linearise zetaS
  trace[Clap.Compiler.reduce.linearise] m!"[linearise]:\n{skipIdentity zetaS lineariseS}"

  let foldProjsS ← foldProjs lineariseS
  trace[Clap.Compiler.reduce.foldProjs] m!"[foldProjs]:\n{skipIdentity lineariseS foldProjsS}"

  let letSomeS ← letSome foldProjsS
  trace[Clap.Compiler.reduce.letSome] m!"[letSome]:\n{skipIdentity foldProjsS letSomeS}"

  return letSomeS
  where
    _sansOuterBinders (e : Expr) : Expr :=
      match e with
      | .lam (body := body) .. | .forallE (body := body) .. =>
        _sansOuterBinders body
      | _ => e
    skipIdentity (σ₁ σ₂ : Expr) := if σ₁ == σ₂ then m!"<Identity>" else m!"{σ₂}"

def reduceExpr (e : Expr) : MetaM Expr := do
  let numIters := 256
  withTraceNode `Clap.Compiler.reduce
    (return m!"{Except.emoji ·} Reducing up to n = {numIters}") do
  let mut res := e
  for i in [0:numIters] do
    let res' ← reduceStep res
    if res == res' then
      trace[Clap.Compiler.reduce.trace.numIters] m!"Reduction done after {i} iterations"
      break
    res := res'
  return res

open MVarId in
def _root_.Lean.MVarId.reduceTarget (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget (f := reduceExpr)

open Elab Tactic in
elab "test_reduce" : tactic => do
  liftMetaTactic' MVarId.reduceTarget

end Clap
