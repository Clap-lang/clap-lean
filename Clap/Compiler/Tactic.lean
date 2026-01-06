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
  let (``Clap.Simulation.s_bisim, ⟨_ :: _ :: lhs :: _⟩) := Expr.getAppFnArgs conclusion
    | throwError m!"{conclusion} is not `Simulation.s_bisim.\nRaw expr: {repr conclusion}."
  return lhs

def putOnTopIdx (n : ℕ) (goals : List MVarId) : List MVarId :=
  goals[n]! :: goals.eraseIdx n

def unassignedGoals (goals : List MVarId) : MetaM (List MVarId) :=
  goals.filterM (not <$> ·.isAssigned)

def putOnTop (what : Expr → Bool) (goals : List MVarId) : MetaM (List MVarId) := do
  if goals.isEmpty then return []
  let n := (←goals.mapM (·.getType')).findIdx what
  if n == goals.length then throwError m!"No bisimulation goal in:\n{goals}"
  return putOnTopIdx n goals

structure Goals where
  inference : Option MVarId
  rest : List MVarId
  deriving Repr

namespace Goals

def unassignedGoals (goals : Goals) : MetaM Goals :=
  Clap.unassignedGoals goals.rest <&> ({goals with rest := ·})

def toLeanGoals (goals : Goals) : List MVarId :=
  goals.inference.toList ++ goals.rest

def runTactic (goals : Goals) (lem : Syntax) : MetaM Goals := do
  let .some inferenceGoal := goals.inference | return goals
  let (inferenceGoals, _) ← inferenceGoal.withContext do
    Elab.runTactic inferenceGoal (←`(tactic|$(⟨lem⟩)))
  match inferenceGoals with
  | [] => return {goals with inference := .none}
  | inferenceGoals =>
    let newInference :: restInference ← putOnTop (·.isAppOf ``Clap.Simulation.s_bisim) inferenceGoals
      | throwError m!"Logic error: `putOnTop should have thrown a 'no bisimulation error'"
    return {goals with inference := newInference, rest := goals.rest ++ restInference}

def seqTacs (goals : Goals) : List Syntax → MetaM Goals
  | [] => pure goals
  | tac₁ :: rest => goals.runTactic tac₁ <|> seqTacs goals rest

end Goals

open Elab Tactic in
/--
Use `lhs` for granular control over matching if needed.
-/
def step (goals : Goals) (lhs : Option Expr := .none) : MetaM Goals := do
  goals.seqTacs
    [
      (←`(tactic|apply $(mkIdent `circuit_ext)
                        (h := $(mkIdent `Simulation.s_bisim.lam) fun _ ↦ ?rest))),
      (←`(tactic|apply $(mkIdent `abc))),
      (←`(tactic|apply $(mkIdent `equiv_eq0)
                         (er := $(mkIdent `Exp.c) _)
                         (he := rfl)))
    ]
  -- goalsOfTac
  --   (←`(tactic|apply $(mkIdent `circuit_ext)
  --                       (h := $(mkIdent `Simulation.s_bisim.lam) fun _ ↦ ?rest)))
  --   goals
  -- <|>
  -- goalsOfTac (←`(tactic|apply $(mkIdent `abc))) goals
  -- <|>
  -- goalsOfTac (←`(tactic|apply $(mkIdent `equiv_eq0)
  --                               (er := $(mkIdent `Exp.c) _)
  --                               (he := rfl))) goals

open Expr in
def extractTac (inferenceGoal : MVarId) : MetaM Goals := do
  let mut goals : Goals := ⟨inferenceGoal, []⟩
  -- let mut i := 0
  while true do
    match goals.inference with
    | .none => break
    | .some inference => goals ← Goals.unassignedGoals =<<
                                   step goals (←lhsOfBisim (←inference.getType'))
                        --  i := i + 1
    -- if i == 2 then break
  return goals

open Elab Tactic in
elab "extract" "using" name:ident : tactic => do
  evalTactic (←`(tacticSeq|unfold $name
                           constructor))
  let (proof :: rest) ← getUnsolvedGoals | throwError "Expected two goals; proof and witness."
  extractTac proof >>= setGoals ∘ (·.toLeanGoals ++ rest)
  evalTactic (←`(tactic|any_goals rfl))

section EXAMPLES

lemma equiv_lam {α : Type} {f : F → α} {g : F → Circuit F F} {x : F}
  (h : Simulation.s_bisim (f x) (Circuit.eval (g x))) :
  Simulation.s_bisim f (Circuit.eval (Circuit.lam g)) := by sorry

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (h : Simulation.s_bisim f (Circuit.eval (Circuit.lam g)))
  (hint : g' = Circuit.lam g) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

def ex₁ (i: F) : Option Unit := do
  -- eq0 i
  accept ()

def ex₂ (i: F) : Option Unit := do
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
  eq0 i
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

lemma equiv_eq0_cheat {el:F} {er:Exp F F} {cl:Option Unit} (cr:Circuit F F)
   (hc: Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil)) :
  Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := sorry

lemma abc :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil) := by
  constructor

def extract_manual₁ :
  { c:Circuit F F // Simulation.s_bisim (ex₁ (F := F)) c.eval } := by
  unfold ex₁
  refine ⟨?c,?p⟩
  case' p =>
    apply circuit_ext (h := Simulation.s_bisim.lam (fun X ↦ ?rest))
  case rest =>
    apply abc
  rfl

def extract_automatic₁ :
  { c:Circuit F F // Simulation.s_bisim (ex₁ (F := F)) c.eval } := by
  extract using ex₁

def extract_automatic₂ :
  { c:Circuit F F // Simulation.s_bisim (ex₂ (F := F)) c.eval } := by
  extract using ex₂

#print extract_automatic₁
#print extract_automatic₂

def extract_manual :
  { c:Circuit F F // Simulation.s_bisim (ex₂ (F := F)) c.eval } := by
  unfold ex₂
  refine ⟨?c,?p⟩
  -- case' p =>
  swap
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?rest)
  skip
  rotate_right 2
  -- case' rest =>
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply abc
  swap
  rfl

end EXAMPLES

end Clap
