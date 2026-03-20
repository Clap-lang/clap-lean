import Lean
import Qq
import Clap.Spec
import Clap.Lang
import Clap.Compiler.Wheels

open Lean Qq Meta Elab

namespace Clap.Compiler

def isNameFormer (e : Expr) (typeName : Name) : MetaM Bool :=
  forallTelescopeReducing e fun _ ret ↦ return ret.isAppOf typeName

def isBind (e : Expr) : MetaM Bool :=
  isDefEq e.getAppFn (.const ``Bind.bind [0, 0])

/--
Defined to be (`lhs : m α`, `rhs`, `α`)
-/
def getBindArgs! (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let firstExplicitArg := (←getFunInfo e.getAppFn).paramInfo.findIdx (·.binderInfo.isExplicit)
  let args := e.getAppArgs
  return (args[firstExplicitArg]!, args[firstExplicitArg + 1]!, (←inferType args[firstExplicitArg]!).getAppArgs.back!)

def getBindArgs? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if ←isBind e
  then getBindArgs! e
  else return .none

def isStructuralBind (e : Expr) : MetaM Bool := do
  let .some (bindLhs, _) ← getBindArgs? e | return false
  let some := Expr.const ``Option.some [0]
  isDefEq bindLhs.getAppFn some

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
def isArith (e : Expr) : Bool :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HPow.hPow, ``OfNat.ofNat,
   ``HDiv.hDiv, ``Div.div].map e.isAppOf |>.any (·==true)

/--
Let `simp` do its job.
-/
def isIterating (e : Expr) : Bool :=
  [
    ``List.toArray, ``Array.size, ``Array.foldr,
    ``Array.foldl, ``Array.map, ``Array.zipWith,
    ``Array.mapIdx, ``Array.take, ``Array.range,
    ``Array.drop, ``Array.set, ``HAppend.hAppend,
    ``Option.getD, --``Array.tail,
    ``Min.min,
    ``GetElem.getElem, ``GetElem?.getElem?, ``GetElem?.getElem!
  ].map e.isAppOf |>.any (·==true)

def isConstant (e : Expr) : Bool :=
  match e with
  | .const name _ => (`Clap.Poseidon.Constant).isPrefixOf name
  | _ => false

def _root_.Lean.Expr.isIrreducibleExpr (e : Expr) : MetaM Bool := do
  e.getAppFn.constName?.elim (return false) isIrreducible

def unfoldAnyStep (e : Expr) : MetaM TransformStep := do
  if isIterating e then return .continue
  if isArith e then return .continue
  -- if isConstant e then return .continue
  if (←isInstance e.getAppFn.constName) then return .continue
  if (←e.isIrreducibleExpr) || (←isVerboten e) then return .continue
  match ← reduceMatcher? e with
  | .reduced v =>
         return .done v
  | _ => let some v ← unfoldDefinition? e | return .continue
         trace[Clap.Compiler.reduce.unfoldAny.const] m!"{e}"
         return .done v

def unfoldAny (e : Expr) : MetaM Expr := do
  Trace.withReportSizeDelta (descr := "unfoldAny") e <| fun e ↦
  -- tryCatchRuntimeEx (do
    Meta.transform e (skipConstInApp := true) (pre := unfoldAnyStep)
  -- ) fun _ ↦ do trace[Clap.Compiler.reduce.unfoldAny] "Timeout[unfold]."; return e

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

-- partial def zeta (e : Expr) : MetaM Expr := do
--   match e with
--   | .letE declName type value body nondep =>
--     if !value.isApp then zeta (body.instantiate1 value) else
--     if ←blacklist.anyM value.getAppFn.isAppOfUptoDefEq then
--       return Expr.letE declName type (←zeta value) (←zeta body) nondep
--     zeta (body.instantiate1 value)
--   | .app fn arg => return .app (← zeta fn) (← zeta arg)
--   | .lam binderName binderType body binderInfo =>
--     return .lam binderName binderType (←zeta body) binderInfo
--   | .forallE binderName binderType body binderInfo =>
--     return .forallE binderName binderType (←zeta body) binderInfo
--   | _ => return e
--   where blacklist := Expr.const (us := []) <$> [
--     ``Spec.Compiler.isZero,
--     ``Spec.Compiler.share]

partial def zeta (e : Expr) : MetaM Expr := do return e

def linearise (e : Expr) : MetaM Expr := do
  Meta.transform (skipConstInApp := true) e fun e ↦ do
    let .some (lhs, rhs, _) ← getBindArgs? e | return .continue
    let .some (lhs', rhs', lamArgT) ← getBindArgs? lhs | return .continue
    let binderName ← getUnusedUserName `x
    withLocalDecl binderName .default lamArgT fun fvar ↦ do
      let lam ← mkLambdaFVars #[fvar] (←mkAppM ``Bind.bind #[.app rhs' fvar, rhs])
      return .visit (←Core.betaReduce (←mkAppM ``Bind.bind #[lhs', lam]))

lemma _root_.Option.some_bind {α β : Type} (x : α) (f : α → Option β) :
  Option.some x >>= f = f x := by simp

def letSome (e : Expr) : MetaM Expr := do
  Meta.transform (skipConstInApp := true) e fun e ↦ do
    if !(←isStructuralBind e) then return .continue
    let (lhs, rhs, _) ← getBindArgs! e
    /-
    We are being naughty. This is not definitionally equal, but we are pretending this is.
    It is perfectly fine for the compiler, but e.g. `test_reduce` now makes the kernel unhappy.

    `_proof` is why these things are equal and `_realTerm` is a term with which
    the kernel would be happy. Nevertheless, we ignore this for the time being.
    
    let _proof ← mkAppM ``Option.some_bind #[lhs.getAppArgs[1]!, rhs]
    let _realTerm := ←e.rewrite _proof
    -/
    return .visit (←Core.betaReduce (.app rhs (lhs.getAppArgs[1]!)))

dsimproc_decl _root_.Array.reduceRange (Array.range _) := fun e ↦ do
  let_expr Array.range k ← e | return .continue
  let l := Array.range k.nat?.get!
  return .visit (Lean.toExpr l)

attribute [simproc] _root_.Array.reduceRange

opaque ABC {α : Type} : α → Prop

set_option hygiene false in
def simpClosed : TermElabM (TSyntax `tactic) :=
  `(tactic|
    simp -failIfUnchanged -singlePass -implicitDefEqProofs +zeta
         -arith -ground +autoUnfold +unfoldPartialApp -locals only
         [-Option.bind_eq_bind, -ZMod, -List.map, -List.zipWith, -List.foldr, -List.length, -Bind.bind,
          -OfNat.ofNat, -Nat.rec,
          List.map_toArray, List.map_cons, id_eq, List.map_nil, List.size_toArray, List.length_cons,
          List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.add_one_sub_one,
          Array.reduceRange, List.append_toArray, List.cons_append, List.nil_append, List.foldl_toArray',
          List.foldl_cons, mul_zero, mul_one, Nat.reduceMul, List.foldl_nil,
          Array.size_zipWith, Array.mapIdx_mapIdx, Array.map_id_fun,
          Array.map_id_fun', Array.size_mapIdx, Array.size_map, Array.reduceGetElem!,
          add_zero, List.mapIdx_toArray, List.mapIdx_cons, List.mapIdx_nil,
          Nat.ofNat_pos, getElem!_pos, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ,
          getElem?_pos, Option.getD_some, List.zipWith_toArray, List.zipWith_cons_cons,
          List.zipWith_nil_right, min_self, List.foldr_toArray', List.foldr_cons, List.foldr_nil,
          Nat.one_lt_ofNat, List.getElem_cons_succ, Nat.lt_add_one]
  )

set_option hygiene false in
def simpOpen : TermElabM (TSyntax `tactic) :=
  `(tactic|simp? -failIfUnchanged
                 -singlePass
                 -implicitDefEqProofs
                 +zeta
                 -arith
                 -ground
                 +autoUnfold
                 -unfoldPartialApp
                 -locals
                 [-Option.bind_eq_bind, -ZMod, -List.map, -List.zipWith, -List.foldr])

set_option hygiene false in
def simplify (e : Expr) (allowPropositionalReasoning : Bool := false) : TermElabM Expr := do
  Trace.withReportSizeDelta e (descr := "simplify") fun e ↦ do
  let isOption ← forallTelescopeReducing (←inferType e) fun _ body ↦ return body.isAppOf ``Option
  if !isOption then return e
  let cfg : Simp.Config := default
  let ctx ← mkSimpContext (simpOnly := true)
                          (cfg := {
                            cfg with zeta := false,
                                     singlePass := false,
                                     maxSteps := 10^6
                            })
  -- let ctx ← mkSimpContext (simpOnly := !allowPropositionalReasoning)
  --                         (cfg := {
  --                           cfg with zeta := false,
  --                                    singlePass := true,
  --                                    maxSteps := 10^6
  --                           })
  if allowPropositionalReasoning
  then
    lambdaTelescope e fun args body ↦ do
      let abc ← mkAppM ``ABC #[body]
      let mvar ← mkFreshExprMVar (.some abc) MetavarKind.syntheticOpaque
      -- tryCatchRuntimeEx ( do
        let ([mvar], _) ←
          Elab.runTactic mvar.mvarId! (←simpClosed) (←read) (←get) |
            throwError "Simp generated more than a single goal on:\n{e}"
        -- let x ← Core.getMessageLog
        -- logWarning m!"What is this: {x.toArray.map (·.data)}"
        let_expr ABC _ x := ←instantiateMVars (←mvar.getType) | throwError "What"
        mkLambdaFVars args x
      -- ) fun _ ↦ do trace[Clap.Compiler.reduce] "Timeout[simp]."
      --              tryCatchRuntimeEx (do return (←Meta.dsimp e ctx).1) fun _ ↦ do
      --                trace[Clap.Compiler.reduce] "Timeout[dsimp]."
      --                return e
  else return (←Meta.dsimp e ctx).1

def reduceStep (e : Expr) : TermElabM Expr := do
  let dsimpS ← withTraceNode `Clap.Compiler.simplify Trace.formatExprWith do
    simplify e (allowPropositionalReasoning := true)
  -- trace[Clap.Compiler.reduce.simplify] m!"{skipIdentity e dsimpS}"
  
  let unfoldAnyS ← withTraceNode `Clap.Compiler.reduce Trace.formatExprWith do
    unfoldAny dsimpS
  -- trace[Clap.Compiler.reduce.unfoldAny] m!"{skipIdentity dsimpS unfoldAnyS}"

  -- let unfoldAnyS ← pure dsimpS
  -- trace[Clap.Compiler.reduce.unfoldAny] m!"{skipIdentity dsimpS unfoldAnyS}"

  -- let betaS ← Core.betaReduce unfoldAnyS
  -- trace[Clap.Compiler.reduce.beta] m!"{skipIdentity unfoldAnyS betaS}"

  -- let zetaS ← zeta betaS
  -- trace[Clap.Compiler.reduce.zeta] m!"{skipIdentity betaS zetaS}"

  -- let lineariseS ← linearise zetaS
  -- trace[Clap.Compiler.reduce.linearise] m!"{skipIdentity zetaS lineariseS}"

  -- let foldProjsS ← foldProjs lineariseS
  -- trace[Clap.Compiler.reduce.foldProjs] m!"{skipIdentity lineariseS foldProjsS}"

  -- let letSomeS ← letSome foldProjsS
  -- trace[Clap.Compiler.reduce.letSome] m!"{skipIdentity foldProjsS letSomeS}"

  let foldProjsS ← foldProjs unfoldAnyS
  trace[Clap.Compiler.reduce.foldProjs] m!"{skipIdentity unfoldAnyS foldProjsS}"

  return foldProjsS

  -- return unfoldAnyS

  -- let zetaS ← zeta foldProjsS
  -- trace[Clap.Compiler.reduce.zeta] m!"{skipIdentity foldProjsS zetaS}"

  -- return zetaS

  -- return unfoldAnyS
  where 
    _sansOuterBinders (e : Expr) : Expr :=
      match e with
      | .lam (body := body) .. | .forallE (body := body) .. =>
        _sansOuterBinders body
      | _ => e
    skipIdentity (σ₁ σ₂ : Expr) := if σ₁ == σ₂ then m!"<Identity>" else m!"{σ₂}"

def reduceExpr (iters : ℕ) (e : Expr) : TermElabM (Expr × ℕ) := do
  let mut res := e
  let mut i := 0
  while i < iters do
    let res' ← reduceStep res
    i := i + 1
    if res == res' then
      trace[Clap.Compiler.reduce.numIters] m!"Reduction done after {i} iterations"
      break
    res := res'
  return (res, i)

open MVarId in
def _root_.Lean.MVarId.reduceTarget (iters : ℕ) (goal : MVarId) : TermElabM MVarId := do
  let tag ← goal.getTag
  let type ← goal.getType
  let (typeNew, _) ← reduceExpr iters type
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew tag
  goal.assign mvarNew
  return mvarNew.mvarId!

open Elab Tactic in
elab "test_reduce" n:num : tactic => do  
  replaceMainGoal [←MVarId.reduceTarget n.getNat (←getMainGoal)]

end Clap.Compiler
