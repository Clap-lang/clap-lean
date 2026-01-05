import Lean
import Qq

import Clap.Simulation

open Lean Qq

namespace Clap

variable {F:Type} [Field F] [DecidableEq F]

def eq0 (e:F) : Option Unit :=
  if e = 0 then some () else none

def accept : Unit -> Unit := fun () => ()

partial def lhsOfBisim (conclusion : Expr) : MetaM Expr := do
  let e ← instantiateMVarsQ (α := q(Prop)) conclusion
--  logInfo m!"===={repr e}"
  match e with
  | ~q(Simulation.s_bisim $lhsQ _) => logInfo "done"; pure lhsQ
  | .app a b =>
      logInfo m!"app |{repr a}| |{b}|"
      if a.isAppOf `Clap.Simulation.s_bisim then
        logInfo m!"app matched!!!!!!!!!!!!"
        pure a
      else
      lhsOfBisim a
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
  inference : Option MVarId -- lhs of bisim, none for the base case
  witness : MVarId -- rhs of bisim
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

-- the 0 here is the index of the newWitness to use in apply
def processLambda : Lemma :=
  .ofUnhygienic
    `($(mkIdent `circuit_ext) ($(mkIdent `Simulation.s_bisim.lam) fun _ ↦ ?_))
    (.some (`($(mkIdent `Circuit.lam)), 0))

def processFinish : Lemma :=
  .ofInference `($(mkIdent `abc))

def processEq0 : Lemma :=
  .ofUnhygienic `($(mkIdent `equiv_eq0) (er := $(mkIdent `Exp.c) h) ($(mkIdent `Simulation.s_bisim.lam) fun _ ↦ ?_))
    _
   -- apply equiv_eq0 (er:=Exp.c h) (he:=rfl) (hc:=?rest1)


end Interface

open Interface

open Elab Tactic in
def step (goals : Goals) (lhs : Expr) : MetaM Goals := do
  logInfo m!"step {lhs}"
  match lhs with
  | .lam .. => logInfo m!"step.lam" ; processLambda.apply goals
  | .app fn arg =>
    let name := fn.getAppFn.constName
    let (arg₁, args) := arg.getAppFnArgs
    if name == `Option.some && arg₁ == `Clap.accept && args == #[q(())]
    then processFinish.apply goals
    else
    /-if name == `Option.bind && arg₁ == `Clap.accept && args == #[q(())]
    then (processFinish `equiv_eq0).apply goals
    else-/ return {goals with inference := .none}
  | _ => logInfo m!"{lhs} is not recognised"; return goals

open Expr in
def extractTac (inferenceGoal witnessGoal : MVarId) : MetaM Goals := do
  let mut goals : Goals := ⟨inferenceGoal, witnessGoal, []⟩
  while true do
    logInfo m!"new goal {goals.inference}"
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

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (h : Simulation.s_bisim f (Circuit.eval (Circuit.lam g)))
  (hint : g' = Circuit.lam g) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

def ex (i: F) : Option Unit := do
  eq0 i
  accept ()

lemma equiv_eq0 {el:F} {er:Exp F F} {cl:Option Unit} (cr:Circuit F F)
  (he: el = Exp.eval er)
  (hc: Simulation.s_bisim cl (Circuit.eval cr)) :
  Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  simp only [Circuit.eval,Option.bind,eq0]
  split
  split
  case _ _ heq her =>
    rw [her] at he
    rw [he] at heq
    simp at heq
  case _ _ hel her =>
    constructor
  case _ _ _ hel =>
    simp at hel
    rw [he] at hel
    simp
    split
    . apply hc
    . contradiction

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
    apply circuit_ext (h := Simulation.s_bisim.lam (fun X ↦ ?rest))
  case' c =>
    apply Circuit.lam
  case' rest =>
    apply equiv_eq0 (er:=Exp.c X) (he:=rfl) (hc:=?rest1)
  swap
  apply abc
  swap
  rfl

end EXAMPLES

end Clap
