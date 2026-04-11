import Lean
import Qq
import Clap.Spec
import Clap.Lang
import Clap.Compiler.Wheels
import Clap.Compiler.Subexpression
import Clap.Test.Compilation.SimpSets

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
    ``Array.size, ``Array.foldr, ``List.toArray,
    ``Array.foldl, ``Array.map, ``Array.zipWith,
    ``Array.mapIdx, ``Array.take, ``Array.range,
    ``Array.drop, ``Array.set, ``HAppend.hAppend, ``Array.set!,
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
  | .reduced v => return .done v
  | _ => let some v ← unfoldDefinition? e | return .continue
         trace[Clap.Compiler.reduce.unfoldAny.const] m!"{e.getAppFn}"
         return .done v

def unfoldAny (e : Expr) : MetaM Expr := do
  Trace.withReportSizeDelta (descr := "unfoldAny") e fun e ↦ do
    let transform := Meta.transform e (skipConstInApp := true) (pre := unfoldAnyStep)
    let options ← getOptions
    if options.getBool `Clap.Compiler.Debug.revertOnTimeout
    then
      tryCatchRuntimeEx transform fun _ ↦ do
        trace[Clap.Compiler.Debug.revertOnTimeout] "unfoldAny - Revert + Continue."
        return e
    else transform

-- #check Expr.forEachWhere
-- #check Expr.findExt?
-- #check Expr.getUsedConstants
-- def nextConstantCbv (e : Expr) : MetaM (Option Name) := do
--   return e.findExt? fun e ↦ if e.isConst then _ else _


  -- logInfo m!"Visiting:\n{e}"
  -- match e with
  -- | .app fn arg =>
  --   nextConstantCbv arg <|> nextConstantCbv fn
  -- | .lam _ _ body _ =>
  --   nextConstantCbv body
  -- | .const declName _ => return .some declName
  -- | .forallE .. -- Does not occur in our context, I hope anyway.
  -- | .letE .. -- Handled by `simp +zeta`, I hope anyway.
  -- | .fvar _
  -- | .mvar _
  -- | .sort _
  -- | .lit _
  -- | .mdata ..
  -- | .proj ..
  -- | .bvar _ => return .none

-- #check Array.set

-- -- def isReducingWithoutUnfolds (e : Expr) : MetaM Bool := do


-- -- def unfoldAnyStep (e : Expr) : MetaM TransformStep := do
-- --   if isIterating e then return .continue
-- --   if isArith e then return .continue
-- --   -- if isConstant e then return .continue
-- --   if (←isInstance e.getAppFn.constName) then return .continue
-- --   match ← reduceMatcher? e with
-- --   | .reduced v => return .done v
-- --   | _ => let (f, args) := e.getAppFnArgs
-- --          if f.isAnonymous then return .continue
-- --          for arg in args do
-- --            let argT ← inferType arg
-- --            let () -- F p | Array
-- --          _

--   -- if (←e.isIrreducibleExpr) || (←isVerboten e) then return .continue
--   -- match ← reduceMatcher? e with
--   -- | .reduced v => return .done v
--   -- | _ => let some v ← unfoldDefinition? e | return .continue
--   --        trace[Clap.Compiler.reduce.unfoldAny.const] m!"{e.getAppFn}"
--   --        return .done v

-- def unfoldAny (e : Expr) : MetaM Expr := do
--   Trace.withReportSizeDelta (descr := "unfoldAny") e fun e ↦ do
--     let transform := Meta.transform e (skipConstInApp := true) (pre := unfoldAnyStep)
--     let options ← getOptions
--     if options.getBool `Clap.Compiler.Debug.revertOnTimeout
--     then
--       tryCatchRuntimeEx transform fun _ ↦ do
--         trace[Clap.Compiler.Debug.revertOnTimeout] "unfoldAny - Revert + Continue."
--         return e
--     else transform

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

dsimproc_decl _root_.Array.reduceRange (Array.range _) := fun e ↦ do
  let_expr Array.range k ← e | return .continue
  let l := Array.range k.nat?.get!
  return .visit (Lean.toExpr l)

attribute [simproc] _root_.Array.reduceRange

-- dsimproc_decl _root_.List.reduceRange (List.range _) := fun e ↦ do
--   let_expr List.range k ← e | return .continue
--   let l := List.range k.nat?.get!
--   return .visit (Lean.toExpr l)

-- attribute [simproc] _root_.List.reduceRange

opaque ABC {α : Type} : α → Prop

set_option hygiene false in
def simpClosed : TermElabM (TSyntax `tactic) :=
  `(tactic|
    simp (config := {
            maxSteps := 10000000
            failIfUnchanged := false
            singlePass := false
            implicitDefEqProofs := false
            arith := false
            ground := false
            zeta := true
            autoUnfold := true
            unfoldPartialApp := true
            locals := false
          }) only
         [unfoldStuff,
          -Option.bind_eq_bind, -ZMod, -List.map, -List.zipWith, -List.foldr, -List.length, -Bind.bind,
          -OfNat.ofNat, -Nat.rec,
          List.map_toArray,
          List.map_cons, List.map_nil,
          id_eq,
          List.size_toArray,
          List.length_cons,
          List.length_nil,
          zero_add,
          Nat.reduceAdd,
          Nat.reduceSub,
          Nat.reduceDiv,
          Nat.add_one_sub_one,
          Array.reduceRange, List.reduceRange,
          List.append_toArray,
          List.cons_append, List.nil_append,
          List.foldl_toArray',
          List.foldl_cons, List.foldl_nil,
          mul_zero, mul_one, Nat.reduceMul,
          Array.size_zipWith, Array.mapIdx_mapIdx, Array.map_id_fun,
          Array.map_id_fun', Array.size_mapIdx, Array.size_map, -- Array.reduceGetElem!,
          add_zero, List.mapIdx_toArray, List.mapIdx_cons, List.mapIdx_nil,
          Nat.ofNat_pos, getElem!_pos, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ,
          getElem?_pos, Option.getD_some, List.zipWith_toArray, List.zipWith_cons_cons,
          List.zipWith_nil_right, min_self, List.foldr_toArray', List.foldr_cons, List.foldr_nil,
          Nat.one_lt_ofNat, List.getElem_cons_succ, Nat.lt_add_one,
          poseidonBN254, poseidon, poseidonEx, mix, ark, sigma, mixLast, liftArr, liftMat,
          Array.set!_eq_setIfInBounds, List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero,
          Clap.Lang.F.assert_eq, Function.comp, Array.sum, List.toArray]
  )

set_option hygiene false in
def simpClosedPoseidon : TermElabM (TSyntax `tactic) :=
  `(tactic|
  simp (config :=
  {
    maxSteps            := 10000000
    failIfUnchanged     := false
    singlePass          := false
    implicitDefEqProofs := true
    zeta                := true
    arith               := false
    ground              := false
    autoUnfold          := false
    unfoldPartialApp    := false
    locals              := false
  }) only
  [
    unfoldStuff,

    bind, pure, bind_assoc,
    Option.bind_some, Option.bind_assoc, Option.getD_some, Option.getD_none,
    id_eq, getElem!_pos, getElem!_neg, getElem?_pos, getElem?_neg,

    List.getElem_cons_succ, List.getElem_cons_zero, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ,
    List.length_cons, List.length_nil,
    List.map_cons, List.map_nil, List.map_id_fun,
    List.mapIdx_nil, List.mapIdx_mapIdx, List.mapIdx_cons,
    List.mapM_nil, List.mapM_cons,
    List.foldl_cons, List.foldl_nil,
    List.foldlM_nil, List.foldlM_cons,
    List.drop_one, List.drop_succ_cons, List.drop_zero,
    List.cons_append, List.nil_append,
    List.reduceRange,
    List.zipWith_cons_cons, List.zipWith_nil_right,
    List.tail_cons, List.tail_nil,
    List.sum_cons, List.sum_nil,
    List.take_succ_cons, List.take_zero,
    List.set_cons_succ, List.set_cons_zero,

    Nat.ofNat_pos, Nat.add_one_sub_one, Nat.one_lt_ofNat,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,

    one_mul, add_zero, zero_lt_one, add_lt_iff_neg_right,
    not_lt_zero, not_false_eq_true, mul_zero, mul_one, lt_self_iff_false,
    zero_tsub, zero_mul, zero_add,

    Function.comp_apply
  ])

set_option hygiene false in
def simpOpen : TermElabM (TSyntax `tactic) :=
  `(tactic|simp (config := {
                    maxSteps := 10000000
                    failIfUnchanged := false
                    singlePass := false
                    implicitDefEqProofs := true
                    zeta := true
                    arith := true
                    ground := false
                    autoUnfold := false
                    unfoldPartialApp := false
                    locals := false
                  }) [Function.comp, Option.bind_assoc, Option.bind_some, Option.some_bind])

set_option hygiene false in
def simpONLY (simpset : Name) : TermElabM (TSyntax `tactic) :=
  let simpset : Ident := mkIdent simpset
  `(tactic|simp (config := {
                   maxSteps := 10000000
                   failIfUnchanged := false
                   singlePass := false
                   implicitDefEqProofs := true
                   zeta := true
                   arith := true
                   ground := false
                   autoUnfold := false
                   unfoldPartialApp := false
                   locals := false}) only
                 [$simpset:ident])

set_option hygiene false in
def simplify (simpSet : Name) (e : Expr) : TermElabM Expr := do
  -- IO.println s!"Simplifying: {←PrettyPrinter.ppExpr e}\nArg: {arg}"
  trace[Clap.Compiler.reduce.simplify.exprSizesBeforeSimplify] m!"[size {e.sizeWithoutSharing}/{←e.numObjs}]"
  let (e, Δheartbeats) ← withHeartbeats do
    Trace.withReportSizeDelta e (descr := "simplify") fun e ↦ do
    -- let isOption ← forallTelescopeReducing (←inferType e) fun _ body ↦ return body.isAppOf ``Option
    -- if !isOption then return e
    lambdaTelescope e fun args body ↦ do
      let abc ← mkAppM ``ABC #[body]
      let mvar ← mkFreshExprMVar (.some abc) MetavarKind.syntheticOpaque
      let simp := if simpSet == simpAll then simpOpen else simpONLY simpSet
      let ([mvar], _) ←
        Elab.runTactic mvar.mvarId! (←simp) (←read) (←get) |
          throwError "Simp generated more than a single goal on:\n{e}"
      let_expr ABC _ x := ←instantiateMVars (←mvar.getType) | throwError "What"
      mkLambdaFVars args x
  trace[Clap.Compiler.reduce.simplify.countHeartbeats]
    m!"[Δheartbeats {Δheartbeats / readDocsFor_withHeartbeats_constant}]"
  -- IO.println s!"Finished simp:\n{←PrettyPrinter.ppExpr e}\nheartbeats eaten:{Δheartbeats}"
  return e
  where readDocsFor_withHeartbeats_constant := 1000
        simpAll := `simpAll

def reduceStep (e : Expr) (simpSet : Name) : TermElabM Expr := do
  let simplifyS ← Trace.withReportTimeoutAndRevert e "simplify" (
    withTraceNode `Clap.Compiler.reduce.simplify (skipIdentity e) ∘ simplify simpSet
  )

  -- discard (nextConstantCbv simplifyS)

  -- let unfoldAnyS ← Trace.withReportTimeoutAndRevert simplifyS "unfoldAny" (
  --   withTraceNode `Clap.Compiler.reduce.unfoldAny (skipIdentity simplifyS) ∘ liftM ∘ unfoldAny
  -- )
  let unfoldAnyS := simplifyS

  -- let foldProjsS ← Trace.withReportTimeoutAndRevert unfoldAnyS "foldProjsS" (
  --   withTraceNode `Clap.Compiler.reduce.foldProjs (skipIdentity unfoldAnyS) ∘ liftM ∘ foldProjs
  -- )
  let foldProjsS := unfoldAnyS
  return foldProjsS
  where skipIdentity (e : Expr) (res : Except Exception Expr) : TermElabM MessageData :=
    match res with
    | .error err => return err.toMessageData
    | .ok res => return if e == res then m!"Fixpoint" else m!"{res}"

def reduceExpr (iters : ℕ) (e : Expr) (_ : CompileMap) (arg : Name) : TermElabM (Expr × ℕ) := do
  logWarning m!"reduceExpr called with: {e}"
  let mut res := e
  let mut i := 0
  while i < iters do
    let res' ← reduceStep res arg
    i := i + 1
    if res == res' then
      trace[Clap.Compiler.reduce.numIters] m!"Reduction done after {i} iterations"
      break
    res := res'
  return (res, i)

/-
TODO: Maybe fix the interactive version one day.
-/
-- open MVarId in
-- def _root_.Lean.MVarId.reduceTarget (iters : ℕ) (goal : MVarId) : TermElabM MVarId := do
--   let tag ← goal.getTag
--   let type ← goal.getType
--   let (typeNew, _) ← reduceExpr iters type
--   let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew tag
--   goal.assign mvarNew
--   return mvarNew.mvarId!

-- open Elab Tactic in
-- elab "test_reduce" n:num : tactic => do
--   replaceMainGoal [←MVarId.reduceTarget n.getNat (←getMainGoal)]

end Clap.Compiler
