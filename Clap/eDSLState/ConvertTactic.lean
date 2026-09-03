import Clap.eDSLState.Convert

/-!
# Tactics for `ConvertsM` proofs

`clap_step` and `clap_finish` mechanise the forwards proof style: walk the `do` block one
`←` at a time, carrying the facts you still need across each step.

Without them a single monadic step costs about ten lines of bookkeeping (see the blocks in
`Clap/Lang/F/F.lean` that end in `set state := ….getState state; clear this`). With them it
costs one.
-/

namespace Clap

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

/-- The final component of a name, e.g. `Clap.Lang.FB.ConvertsM ↦ "ConvertsM"`. -/
private def lastComponent : Name → String
  | .str _ s => s
  | _ => ""

/--
If `ty` is a `Clap.Converts` — directly, or through a family wrapper such as `F.Converts` —
return the `ClapMState` it is stated at.

The head-name guard keeps us from calling `whnf` on unrelated hypotheses.
-/
private def convertsState? (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const n _ := ty.consumeMData.getAppFn | return none
  unless lastComponent n == "Converts" do return none
  match (← whnf ty).getAppFnArgs with
  | (``Clap.Converts, args) => return args[3]?
  | _ => return none

/-- As `convertsState?`, but for `Clap.ConvertsM` and its family wrappers. -/
private def convertsMState? (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const n _ := ty.consumeMData.getAppFn | return none
  unless lastComponent n == "ConvertsM" do return none
  match (← whnf ty).getAppFnArgs with
  | (``Clap.ConvertsM, args) => return args[4]?
  | _ => return none

/--
`clap_step h` advances a `ConvertsM` goal past one monadic step, where `h` proves the
`ConvertsM` of that step's action.

It applies `Clap.ConvertsM.bind`, leaving the goal at the post-state, and re-bases every
`Converts` hypothesis stated at the pre-state onto the post-state via `ConvertsM.skip`.
Anything you still need after the step must therefore be a `Converts` fact — that is the
one thing the frame rule transports.

`clap_step h with hr` also names the step's own result `hr : Converts … (post-state) …`.

There is no need to keep `wellFormed`/`constraints` facts around: unlike the hand-rolled
style, `ConvertsM.bind` discharges all three fields of `ConvertsM` itself.
-/
syntax (name := clapStep) "clap_step " term (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| clap_step $h:term $[with $nm:ident]?) => do
    -- The pre-state, read off the goal.
    let pre ← withMainContext do
      let tgt ← instantiateMVars (← getMainTarget)
      let some st ← convertsMState? tgt
        | throwError "clap_step: the goal is not a `ConvertsM`:{indentExpr tgt}"
      instantiateMVars st

    -- Elaborate the step against a type whose state is pinned to the goal's pre-state, so
    -- that a step lemma with an implicit `state` does not have to be given it by hand.
    let hName ← mkFreshUserName `clapStep
    let hId := mkIdent hName
    withMainContext do
      let cinfo ← getConstInfo ``Clap.ConvertsM
      let lvls ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
      let (args, _, _) ←
        forallMetaTelescope (cinfo.type.instantiateLevelParams cinfo.levelParams lvls)
      let some stArg := args[4]? | throwError "clap_step: unexpected `ConvertsM` arity"
      unless ← isDefEq stArg pre do
        throwError "clap_step: could not pin the pre-state{indentExpr pre}"
      let ty := mkAppN (mkConst ``Clap.ConvertsM lvls) args
      let hExpr ← Term.elabTermEnsuringType h (some ty)
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      let hExpr ← instantiateMVars hExpr
      liftMetaTactic fun g => do
        let (_, g) ← (← g.assert hName ty hExpr).intro1P
        return [g]

    -- Every `Converts` hypothesis stated at the pre-state, which the step invalidates.
    let toRebase ← withMainContext do
      let mut out := #[]
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if ldecl.userName == hId.getId then continue
        let some st ← convertsState? (← instantiateMVars ldecl.type) | continue
        if ← isDefEq st pre then
          out := out.push ldecl.userName
      pure out

    evalTactic (← `(tactic| refine Clap.ConvertsM.bind $hId ?_))
    for n in toRebase do
      let nId := mkIdent n
      evalTactic (← `(tactic| replace $nId:ident := Clap.ConvertsM.skip $hId $nId))
    if let some nm := nm then
      evalTactic (← `(tactic| have $nm:ident := Clap.ConvertsM.converts $hId))
    evalTactic (← `(tactic| try clear $hId))

/--
`clap_finish h` closes a `ConvertsM` goal from `h`, the `ConvertsM` of the block's last
action.

If `h`'s spec value differs from the goal's, it goes through `ConvertsM.congr_val` and tries
to close the gap with `rfl`/`simp`/`grind`; failing that it leaves the serialisation equality
as a goal for you to discharge with a separate pure lemma.
-/
syntax (name := clapFinish) "clap_finish " term : tactic

macro_rules
  | `(tactic| clap_finish $h:term) =>
    `(tactic|
        first
          | exact $h
          | exact Clap.ConvertsM.congr_val $h (by first | rfl | simp | grind)
          | refine Clap.ConvertsM.congr_val $h ?_)

end Clap
