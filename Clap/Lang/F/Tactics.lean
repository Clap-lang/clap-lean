import Lean
import Clap.eDSLState.eDSL
import Clap.eDSLState.Convert.Base
import Clap.Lang.F.Extensions


section Helpers

open Lean Elab Tactic Meta

def Lean.Meta.Hypothesis.ofNameValue (userName : Name) (value : Lean.Expr) : MetaM Hypothesis := do
  return {
    userName := userName
    type     := ←inferType value
    value    := value
  }

def Lean.MVarId.set (goal : MVarId) (name : Name) (rhs : Term) : MetaM MVarId := do
  let ident := mkIdent name
  let ([goal], _) ← runTactic goal (←`(tactic| set $ident:ident := $rhs))
    | throwError m!"set failed (rhs := {rhs})"
  return goal

/--
Execute `set`s in order, ensuring the local context is updated between every invocation.
-/
def Lean.MVarId.setManyInOrder (goal : MVarId) (nameXrhs : List (Name × Term)) : MetaM MVarId :=
  nameXrhs.foldlM (fun acc (name, rhs) ↦ do acc.withContext do acc.set name rhs) goal

end Helpers


namespace Clap.Tactic

open Lean Elab Tactic Meta

section Parsing

structure ConvertsArgs where
  p : Lean.Expr
  α : Lean.Expr
  conversion : Lean.Expr
  state : Lean.Expr
  exprs : Lean.Expr
  val : Lean.Expr

structure ConvertsMArgs where
  p : Lean.Expr
  α : Lean.Expr
  conversion : Lean.Expr
  action : Lean.Expr
  state : Lean.Expr
  val : Lean.Expr
  constraints : Lean.Expr

structure ConvertsMExpr where
  args : ConvertsMArgs
  result : Lean.Expr
  wellFormed : Lean.Expr
  constraints : Lean.Expr

def parseConverts (convertsT : Lean.Expr) (goal : MVarId) :
  MetaM (Option ConvertsArgs)
:= goal.withContext do
  let convertsT ← instantiateMVars convertsT
  match_expr convertsT with
  | Clap.Converts p α conversion state exprs val => return .some {
      p := p,
      α := α
      conversion := conversion
      state := state
      exprs := exprs
      val := val
    }
  | _ => return .none

def parseConvertsMArgs (convertsMT : Lean.Expr) (goal : MVarId) :
  MetaM (Option ConvertsMArgs)
:= goal.withContext do
  let convertsMT ← instantiateMVars convertsMT
  match_expr convertsMT with
  | Clap.ConvertsM p α conversion action state val constraints => return .some {
      p,
      α,
      conversion,
      action,
      state,
      val,
      constraints
    }
  | _ => return .none

def parseConvertsM (convertsME convertsMT : Lean.Expr) (goal : MVarId) :
  MetaM (Option ConvertsMExpr)
:= goal.withContext do
  let convertsMT ← instantiateMVars convertsMT
  let args ← parseConvertsMArgs convertsMT goal
  let result ← mkAppM ``Clap.ConvertsM.result #[convertsME]
  let wellFormed ← mkAppM ``Clap.ConvertsM.wellFormed #[convertsME]
  let constraints ← mkAppM ``Clap.ConvertsM.constraints #[convertsME]
  return args.map λ args => {
    args,
    result,
    wellFormed,
    constraints
  }

end Parsing


section Tactic

/--
Yields fvars of local hypotheses of the shape `<_>.Converts`.
Warns if they are over multiple distinct states
-/
def stateAssertions (goal : MVarId) :
  MetaM (Array Lean.Expr)
:= goal.withContext do
  let allAssertions := (←getLCtx).getFVars
  let allAssertionsT ← allAssertions.filterMapM fun fvar ↦ do
    let type ← instantiateMVars (←inferType fvar)
    let args ← parseConverts type goal
    return args.map λ args => (fvar, args)
  if (allAssertionsT.groupByKey (fun (_, args) ↦ args.state) |>.size) > 1
  then
    -- logWarning m!"OUR GUY:\n{(allAssertionsT.groupByKey fun (_, _, st, _) ↦ st).toArray}"
    logWarning m!"Assumptions of shape `Converts` refer to multiple states. Are you ~~mad~~ sure?"
  return allAssertionsT.map Prod.fst

def lemmaOfNextCommand (goal : MVarId) : MetaM (Option Lean.Expr) := do
  let conclusion ← (instantiateMVars (←goal.getType))
  let .some args ← parseConvertsMArgs conclusion goal |
    logWarning m!"Cannot infer the next step - expected `Clap.ConvertsM`.\nGot instead:\n{conclusion}"
    return .none
  let ⟨name, _args⟩ := args.action.getAppFnArgs

  if name == `Bind.bind then
    -- logInfo m!"Bind.bind";
    return mkConst `Clap.convertsM_bind
  if name == `Functor.map then
    -- logInfo m!"Functor.map";
    return mkConst `Clap.convertsM_map

  logWarning m!"Conclusion unchanged; spec missing for:\n{args.action}"
  return .none

/--
Extend me.
-/
elab "constraints" : tactic => do
  evalTactic <| ←`(tactic|
    (
      first
        | (intros; trivial)
        | skip
    )
  )

def step_impl (convertsME : Lean.Expr) (actionName : Name) (goal : MVarId) : TermElabM MVarId := goal.withContext do
  let convertsMType ← inferType convertsME
  let .some convertsM ←
    parseConvertsM convertsME convertsMType goal
    | logError m!"Expected ConvertsM. Got:\n{convertsMType}"
      return goal
  let stateS ← Term.exprToSyntax convertsM.args.state
  let stateAssertions ← stateAssertions goal
  let assertions ← stateAssertions.mapM fun fvar ↦ do
    return (fvar, ←mkAppM `Clap.converts_skip #[convertsME, fvar])
  let goal ← assertions.foldlM (init := goal) fun goal (fvar, _) ↦
    goal.clear fvar.fvarId!

  let (_, goal) ← goal.assertHypotheses <|
    #[
      ←Hypothesis.ofNameValue (actionName.appendBefore "h_") convertsM.result,
      ←Hypothesis.ofNameValue `h_wellFormed convertsM.wellFormed,
      ←Hypothesis.ofNameValue `h_constraints convertsM.constraints,
    ]
    ++ (
      ←assertions.mapM fun (fvar, expr) ↦ do
        let name := ((←getLCtx).get! fvar.fvarId!).userName
        Hypothesis.ofNameValue name expr
    )

  let env ← getEnv
  modifyEnv (fun _ ↦ stepExt.setState env ⟨actionName.appendBefore "h_"⟩)

  let actionIdent := Lean.mkIdent actionName

  goal.setManyInOrder [
    -- `set action := <action_from_monad>`
    (actionName, ←Term.exprToSyntax convertsM.args.action),
    -- `set <action>_result := <action>.getResult <state>.numAlloc <state>.σ`
    (actionName.appendAfter "_result", ←`($(actionIdent).getResult $(stateS).numAlloc $(stateS).σ)),
    -- `set <state> := <action>.getState <state>`
    (actionName.appendAfter "_state", ←`($(actionIdent).getState $stateS))
  ]

elab "step" convertsM:term "as" actionName:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let convertsME ← instantiateMVars (←elabTerm convertsM .none)
  discard do
    match ←lemmaOfNextCommand goal with
    | .none => pure ()
    | .some stepConclusion =>
      replaceMainGoal (←goal.apply stepConclusion)
      let goal ← getMainGoal
      let [] := ← goal.apply convertsME | throwError m!"Failed to unify. Bad."
  let goal ← step_impl convertsME actionName.getId (←getMainGoal)
  replaceMainGoal [goal]
  evalTactic (←`(tactic| all_goals constraints))

-- Used for if step is missing functionality for the specific shape of conclusion
elab "step_state" convertsM:term "as" actionName:ident : tactic => withMainContext do
  let convertsME ← instantiateMVars (←elabTerm convertsM .none)
  let goal ← step_impl convertsME actionName.getId (←getMainGoal)
  replaceMainGoal [goal]

-- elab "finish" : tactic => withMainContext do
--   let target ← whnf (←getMainTarget)

--   if !target.isAppOf ``Clap.ConvertsM
--   then logWarning m!"Made no progress - the concluson must be of shape ConvertsM."
--        return ()

--   let result :: goalsRest ← (←getMainGoal).constructor | unreachable!
--   for goal in goalsRest do
--     try
--       let ([], _) ← runTactic goal (←`(tactic| grind)) | continue
--     catch _ =>
--       continue

--   let goalsRest ← goalsRest.filterM fun goal ↦ return !(←goal.isAssigned)

--   let lastConvertsM := stepExt.getState (← getEnv) |>.lastLemmaUserName
--   let lastConvertsME := (←getLCtx).getFromUserName! lastConvertsM |>.toExpr

--   let conclusionT ← result.getType'
--   let_expr Clap.Converts _ _ _ st _ _ := conclusionT |
--     throwError m!"Finish expects Clap.ConvertsM - failed to extract converts. Bad."

--   let lastConvertsMT ← instantiateMVars (←inferType lastConvertsME)
--   let_expr Clap.Converts _ _ _ st' _ _ := lastConvertsMT |
--     throwError m!"Could not extract Clap.Converts from the previous step command. Bad."

--   logInfo m!"st: {st}\nst': {st'}"

--   -- if !(←isDefEq st st')
--   -- then throwError m!"State does not match the state from the previous step. Bad."

--   let ([result], _) ←
--     try
--       runTactic result
--         (←`(tactic| apply Clap.converts_of_converts $(←Term.exprToSyntax lastConvertsME)))
--     catch _ =>
--       return default
--     | logWarning m!"Cannot apply Clap.converts_of_converts"

--   let (goals, _) ← runTactic result (←`(tactic| try with_reducible rfl))
--   replaceMainGoal (goals ++ goalsRest)

end Tactic

end Clap.Tactic
