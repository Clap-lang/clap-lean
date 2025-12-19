import Lean
import Qq

import Clap.Simulation

open Lean Qq

namespace Clap

def accept : Unit -> Unit := fun () => ()

def lhsOfBisim (conclusion : Expr) : MetaM Expr := do
  let e ← instantiateMVarsQ (α := q(Prop)) conclusion
  match e with
  | ~q(Simulation.s_bisim $lhsQ _) => pure lhsQ
  | _ => throwError "{e} is not `Simulation.s_bisim."

def putOnTopIdx (n : ℕ) (goals : List MVarId) : List MVarId :=
  goals[n]! :: goals.eraseIdx n

def putOnTop (what : Expr → Bool) (goals : List MVarId) : MetaM (List MVarId) := do
  if goals.isEmpty then return []
  let n := (←goals.mapM (·.getType')).findIdx what
  if n == goals.length then throwError m!"No bisimulation goal in:\n{goals}"
  return putOnTopIdx n goals

namespace Interface

structure Goals where
  inference : Option MVarId
  witness : MVarId
  rest : List MVarId
  deriving Repr

def Goals.toLeanGoals (goals : Goals) : List MVarId :=
  goals.inference.toList ++ [goals.witness] ++ goals.rest

namespace Goals

end Goals

/--
`ℕ` identifies which subgoal is the next witness.
-/
structure Lemma where
  inference : Syntax
  witness : Option (Syntax × ℕ)
  deriving Repr

namespace Lemma

def ofInference (inference : Unhygienic Syntax) :=
  Lemma.mk inference.run .none

def ofUnhygienic (inference : Unhygienic Syntax) (witness : Option (Unhygienic Syntax × ℕ)) :=
  Lemma.mk inference.run (witness.map (·.map (·.run) id))

def apply (lem : Lemma) (goals : Goals) : MetaM Goals := do
  let .some inferenceGoal := goals.inference | return goals
  let (inferenceGoals, _) ← inferenceGoal.withContext do
    Elab.runTactic inferenceGoal (←`(tactic|apply $(⟨lem.inference⟩)))
  
  match inferenceGoals with
  | [] => return {goals with inference := .none}
  | inferenceGoals =>
    let newInference :: restInference ← putOnTop (·.isAppOf ``Clap.Simulation.s_bisim) inferenceGoals
      | throwError m!"Logic error: `putOnTop should have thrown a 'no bisimulation error'"

    let newWitness :: restWitness ← lem.witness.elim (pure [goals.witness]) fun (witness, newWitnessIdx) ↦ do
      let (goals, _) ← Elab.runTactic goals.witness (←`(tactic|apply $(⟨witness⟩)))
      return putOnTopIdx newWitnessIdx goals
      | throwError m!"{repr lem.witness} failed to generate a witness."

    return ⟨newInference, newWitness, restInference ++ restWitness⟩

end Lemma

def processLambda : Lemma :=
  .ofUnhygienic
    `($(mkIdent `circuit_ext) ($(mkIdent `Simulation.s_bisim.lam) fun _ ↦ ?_))
    (.some (`($(mkIdent `Circuit.lam)), 0))
      
def processFinish : Lemma :=
  .ofInference `($(mkIdent `abc))

end Interface

open Interface

open Elab Tactic in
def step (goals : Goals) (lhs : Expr) : MetaM Goals := do
  match lhs with
  | .lam .. => processLambda.apply goals
  | .app fn arg =>
    let name := fn.getAppFn.constName
    let (arg₁, args) := arg.getAppFnArgs
    if name == `Option.some && arg₁ == `Clap.accept && args == #[q(())]
    then processFinish.apply goals
    else return {goals with inference := .none}
  | _ => logInfo m!"{lhs} is not recognised"; return goals

open Expr in
def extractTac (inferenceGoal witnessGoal : MVarId) : MetaM Goals := do
  let mut goals : Goals := ⟨inferenceGoal, witnessGoal, []⟩
  while true do
    match goals.inference with
    | .none => break
    | .some inference => goals ← step goals (←lhsOfBisim (←inference.getType))
  return goals

open Elab Tactic in
elab "extract" "using" name:ident : tactic => do
  evalTactic (←`(tacticSeq|unfold $name
                           constructor))
  let (proof :: witness :: rest) ← getUnsolvedGoals | throwError "Expected two goals; proof and witness."
  extractTac proof witness >>= setGoals ∘ (·.toLeanGoals ++ rest)
  evalTactic (←`(tactic|any_goals rfl))

section EXAMPLES

variable {F:Type} [Field F] [DecidableEq F]

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (h : Simulation.s_bisim f (Circuit.eval (Circuit.lam g)))
  (hint : g' = Circuit.lam g) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

def ex (i: F) : Option Unit := do
--  eq0 i
  accept ()

lemma abc :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil) := by
  constructor

def extract_automatic :
  { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
  extract using ex

#print extract_automatic

def extract_manual :
  { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
  unfold ex
  refine ⟨?c,?p⟩
  case' p =>
    apply circuit_ext (h := Simulation.s_bisim.lam (fun h ↦ ?rest))
  case' c =>
    apply Circuit.lam
  case' rest =>
    apply abc
  swap
  rfl

end EXAMPLES

end Clap
