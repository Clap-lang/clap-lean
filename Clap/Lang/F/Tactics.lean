import Lean
import Clap.eDSLState.eDSL
import Clap.eDSLState.Convert
import Clap.Lang.F.Extensions

namespace Clap

section

open Lean Elab Tactic Meta

def baseNamespace := Name.mkStr2 "Clap" "Lang"

def lemmaOfIdentifiers (prefixNamespace lemmaName : Name) : MetaM ConstantInfo := do
  let name := baseNamespace ++ prefixNamespace ++ lemmaName
  let .some «lemma» := (←getEnv).find? name
    | throwError m!"Undeclared constant: {name}"
  return «lemma»

def convertsMargs (convertsME convertsMT : Lean.Expr) (goal : MVarId) :
  MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := goal.withContext do
  -- logInfo m!"In"
  let convertsMT ← instantiateMVars convertsMT
  -- logInfo m!"Instantiated"
  match_expr convertsMT with
  | Clap.ConvertsM p α _ action state _ => return .some (
      -- ←Expr.mkDirectProjection convertsMT `result,
      ←mkAppM ``Clap.ConvertsM.result #[convertsME],
      -- ←Expr.mkDirectProjection convertsMT `wellFormed,
      ←mkAppM ``Clap.ConvertsM.wellFormed #[convertsME],
      -- ←Expr.mkDirectProjection convertsMT `constraints,
      ←mkAppM ``Clap.ConvertsM.constraints #[convertsME],
      p,
      α,
      action,
      state
    )
  | _ => return .none


-- def convertsLemmaAndStateOfType (convertsT : Lean.Expr) : MetaM (ConstantInfo × Lean.Expr) := do
--   let convertsT ← instantiateMVars convertsT
--   let (prefixNamespace, st) :=
--     match_expr convertsT with
--     | Clap.Lang.FList.Converts _ st _ _ => (`FList, st)
--     | Clap.Lang.FArray.Converts _ st _ _ => (`FArray, st)
--     | Clap.Lang.FUnit.Converts _ st _ _ => (`FUnit, st)
--     | Clap.Lang.FB.Converts _ st _ _ => (`FB, st)
--     | Clap.Lang.F.Converts _ st _ _ => (`F, st)
--     | _ => unreachable!
--   return (←lemmaOfIdentifiers prefixNamespace `converts_skip, st)

def _root_.Lean.Meta.Hypothesis.ofNameValue (userName : Name) (value : Lean.Expr) : MetaM Hypothesis := do
  return {
    userName := userName
    type     := ←inferType value
    value    := value
  }

def _root_.Lean.MVarId.set (goal : MVarId) (name : Name) (rhs : Term) : MetaM MVarId := do
  let ident := mkIdent name
  let ([goal], _) ← runTactic goal (←`(tactic| set $ident:ident := $rhs))
    | throwError m!"set failed (rhs := {rhs})"
  return goal

/--
Execute `set`s in order, ensuring the local context is updated between every invocation.
-/
def _root_.Lean.MVarId.setManyInOrder (goal : MVarId) (nameXrhs : List (Name × Term)) : MetaM MVarId :=
  nameXrhs.foldlM (fun acc (name, rhs) ↦ do acc.withContext do acc.set name rhs) goal

/--
Yields tuples `(namespace, fvar, state, type)` of local hypotheses of the shape `<_>.Converts`.
-/
def stateAssertions (goal : MVarId) :
  MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := goal.withContext do
  let allAssertions := (←getLCtx).getFVars
  let allAssertionsT ← allAssertions.filterMapM fun fvar ↦ do
    let type ← instantiateMVars (←inferType fvar)
    return match_expr type with
    | Clap.Converts _ _ _ st _ _ => .some (fvar, st, type)
    | _ => .none
  if (allAssertionsT.groupByKey (fun (_, st, _) ↦ st) |>.size) > 1
  then
    -- logWarning m!"OUR GUY:\n{(allAssertionsT.groupByKey fun (_, _, st, _) ↦ st).toArray}"
    logWarning m!"Assumptions of shape `Converts` refer to multiple states. Are you ~~mad~~ sure?"
  return allAssertionsT

def lemmaOfNextCommand (goal : MVarId) : MetaM (Option Lean.Expr) := do
  let conclusion ← (instantiateMVars (←goal.getType))
  let_expr Clap.ConvertsM _ _ _ action _ _ := conclusion |
    logWarning m!"Cannot infer the next step - expected `Clap.ConvertsM`.\nGot instead:\n{conclusion}"
    return .none
  let ⟨name, _args⟩ := action.getAppFnArgs

  if name == `Bind.bind then logInfo m!"Bind.bind"; return mkConst `Clap.convertsM_bind
  if name == `Functor.map then logInfo m!"Functor.map"; return mkConst `Clap.convertsM_map

  logInfo m!"Conclusion unchanged; spec missing for:\n{action}"
  return .none

def step_impl (convertsME : Lean.Expr) (actionName : Name) (goal : MVarId) : TermElabM MVarId := goal.withContext do
  logInfo m!"GOAL α: {goal}"
  let convertsMType ← inferType convertsME
  logInfo m!"convetsME: {convertsME}\nconvertsMType: {convertsMType}"
  -- logInfo m!"convertsMType : {convertsMType}"
  -- logError m!"Expected ConvertsM. Got:\n{convertsMType}"
  let .some (convertsConvertsM, wellFormedConvertsM, constraintsConvertsM, pE, αE, actionE, stateE) ←
    convertsMargs convertsME convertsMType goal
    | logError m!"Expected ConvertsM. Got:\n{convertsMType}"
      return goal
  let stateS ← Term.exprToSyntax stateE
  let stepE := convertsConvertsM
  let hypWFE := wellFormedConvertsM
  let hypConstraintsE := constraintsConvertsM
  let stateAssertions ← stateAssertions goal
  let assertions ← stateAssertions.mapM fun (fvar, state, type) ↦ do
    return (fvar, ←mkAppM `Clap.converts_skip #[convertsME, fvar])
  let goal ← assertions.foldlM (init := goal) fun goal (fvar, _) ↦
    goal.clear fvar.fvarId!

  let (_, goal) ← goal.assertHypotheses <|
    #[
      ←Hypothesis.ofNameValue (actionName.appendBefore "h_") stepE,
      ←Hypothesis.ofNameValue `h_wellFormed hypWFE,
      ←Hypothesis.ofNameValue `h_constraints hypConstraintsE,
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
    (actionName, ←Term.exprToSyntax actionE),
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

elab "finish" : tactic => withMainContext do
  let target ← whnf (←getMainTarget)

  if !target.isAppOf ``Clap.ConvertsM
  then logWarning m!"Made no progress - the concluson must be of shape ConvertsM."
       return ()

  let result :: goalsRest ← (←getMainGoal).constructor | unreachable!
  for goal in goalsRest do
    try
      let ([], _) ← runTactic goal (←`(tactic| grind)) | continue
    catch _ =>
      continue
  
  let goalsRest ← goalsRest.filterM fun goal ↦ return !(←goal.isAssigned)

  let lastConvertsM := stepExt.getState (← getEnv) |>.lastLemmaUserName
  let lastConvertsME := (←getLCtx).getFromUserName! lastConvertsM |>.toExpr
  
  let conclusionT ← result.getType'
  let_expr Clap.Converts _ _ _ st _ _ := conclusionT |
    throwError m!"Finish expects Clap.ConvertsM - failed to extract converts. Bad."

  let lastConvertsMT ← instantiateMVars (←inferType lastConvertsME)
  let_expr Clap.Converts _ _ _ st' _ _ := lastConvertsMT |
    throwError m!"Could not extract Clap.Converts from the previous step command. Bad."

  logInfo m!"st: {st}\nst': {st'}"

  -- if !(←isDefEq st st')
  -- then throwError m!"State does not match the state from the previous step. Bad."

  let ([result], _) ←
    try
      runTactic result
        (←`(tactic| apply Clap.converts_of_converts $(←Term.exprToSyntax lastConvertsME)))
    catch _ =>
      return default
    | logWarning m!"Cannot apply Clap.converts_of_converts"

  let (goals, _) ← runTactic result (←`(tactic| try with_reducible rfl))
  replaceMainGoal (goals ++ goalsRest)

end

end Clap
