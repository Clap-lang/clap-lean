import Lean
import Qq

import Clap.Simulation

open Lean Qq

namespace Clap

variable {F:Type} [Field F] [DecidableEq F]

@[irreducible]
def eq0 (e:F) : Option Unit :=
  if e = 0 then some () else none

@[irreducible]
def accept : Unit -> Unit := fun () => ()

@[irreducible]
def share (e : F) : Option F := e

@[irreducible]
def is_zero (e:F) : Option F := if e = 0 then .some 1 else .some 0

/--
Assumes `conclusion` has had its mvars instantiated.
-/
partial def lhsOfBisim (conclusion : Expr) : MetaM Expr := do
  let (``Clap.Simulation.s_bisim, ⟨_ :: _ :: lhs :: _⟩) := conclusion.getAppFnArgs
    | throwError m!"{conclusion} is not `Simulation.s_bisim.\nRaw expr: {repr conclusion}."
  return lhs

def putOnTopIdx (n : Nat) (goals : List MVarId) : List MVarId :=
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
  logInfo m!"applied {lem}"
  match inferenceGoals with
  | [] => return {goals with inference := .none}
  | inferenceGoals =>
    let newInference :: restInference ← putOnTop (·.isAppOf ``Clap.Simulation.s_bisim) inferenceGoals
      | throwError m!"Logic error: `putOnTop should have thrown a 'no bisimulation error'"
    return ⟨newInference, goals.rest ++ restInference⟩

def seqTacs (goals : Goals) : List Syntax → MetaM Goals
  | [] => pure goals
  | tac₁ :: rest => goals.runTactic tac₁ <|> seqTacs goals rest

end Goals

set_option hygiene false in -- We'll see about this one, tired of `mkIdent` :).
/--
Use `lhs` for granular control over matching if needed.
-/
def step (goals : Goals) (lhs : Option Expr := .none) : MetaM Goals := do
  goals.seqTacs
    [
      (←`(tactic|apply $(mkIdent `circuit_ext)
                         (h := $(mkIdent `Simulation.s_bisim.lam) fun _ ↦ ?_))),
      (←`(tactic|apply $(mkIdent `equiv_accept))),
      (←`(tactic|apply $(mkIdent `equiv_eq0)
                         (er := $(mkIdent `Exp.c) _)
                         (he := rfl))),
      (←`(tactic|apply $(mkIdent `equiv_share)
                         (er := $(mkIdent `Exp.c) _)
                         (h := rfl)
                         (h₁ := fun _ ↦ ?_))),
      (←`(tactic|apply $(mkIdent `equiv_is_zero)
                         (er := $(mkIdent `Exp.c) _)
                         (he := rfl)
                         (hk := fun _ ↦ ?_)))
    ]

def extractTac (inferenceGoal : MVarId) : MetaM Goals := do
  let mut goals ← curry inferenceGoal
  -- let mut i := 0
  while true do
    match goals.inference with
    | .none => break
    | .some inference => goals ← Goals.unassignedGoals =<<
                                   step goals (←lhsOfBisim (←inference.getType'))
                        --  i := i + 1
    -- if i == 5 then break
  return goals
  -- TODO(workaround) Currently a stopgap measure before we incorporate currying in a better way
  where curry (inferenceGoal : MVarId) : MetaM Goals := do
    let ([inferenceGoal], _) ←
      Elab.runTactic inferenceGoal (←`(tactic|try dsimp -zeta only [$(mkIdent `curry):ident]))
      | throwError m!"Failed to curry {inferenceGoal}"
    return ⟨inferenceGoal, []⟩

open Elab Tactic in
elab "extract" "using" name:ident : tactic => do
  evalTactic (←`(tacticSeq|unfold $name
                           constructor))
  let (proof :: rest) ← getUnsolvedGoals | throwError "Expected two goals; proof and witness."
  extractTac proof >>= setGoals ∘ (·.toLeanGoals ++ rest)
  evalTactic (←`(tactic|any_goals rfl))

section EXAMPLES

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (h : Simulation.s_bisim f (Circuit.eval (Circuit.lam g)))
  (hint : g' = Circuit.lam g) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

lemma equiv_share {el : F} {er : Exp F F} {kl : F → Option Unit} {kr : F -> Circuit F F}
  (h : el = Exp.eval er)
  (h₁ : ∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) :
  Simulation.s_bisim (bind (share el) kl) (Circuit.eval (.share er kr)) := by
  unfold share
  aesop

@[reducible]
def typ (a r:Type) : ℕ -> Type
  | 0   => r
  | n+1 => a -> typ a r n

@[reducible]
def curry {a r:Type} (n:ℕ) (k:Vector a n -> r) : typ a r n :=
  match n with
  | 0 => k ⟨#[], by rfl⟩
  | n+1 => fun x:a => curry n (fun l => k (Vector.push l x) )

def ex₁ (i: F) : Option Unit := do
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

def ex₃ (i : F) : Option Unit := do
  eq0 i
  let vi ← share i
  eq0 (vi + i)
  accept ()

-- This is (eq0 i), but baby steps.
def ex₄ (i : F) : Option Unit := do
  let x ← is_zero i
  eq0 (1 - x)
  accept ()

def ex₅ (is₁ : F) (is₂ : F) : Option Unit := do
  eq0 is₁
  let vi <- share is₁
  eq0 (vi + is₂)
  accept ()

def ex₆ :=
  curry 2 (fun (is : Vector F 2) ↦ do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  return accept ())

def ex₇ :=
  curry 2 (fun (xs: Vector F 2) =>
  curry 2 (fun (ys: Vector F 2) =>
  curry 2 (fun (zs: Vector F 2) => do
  eq0 (zs[0]-xs[1])
  return accept ()
  )))

-- def ex₇' (xs: Vector F 2) (ys: Vector F 2) (zs: Vector F 2) : typ F (typ F (typ F (Option Unit) 2) 2) 2 := _

example {is : Vector F 2} : ex₆ is = ex₅ is[0] is[1] := rfl

-- match first_line
--   | let _ ← isZero => ...
--   |

-- def ex_circuit : Circuit' (F p) := fun _ =>
--   .lam (fun i =>
--   .is_zero (.v i) (fun x ↦
--   .eq0 (1 - .v x)
--   .nil))

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

lemma equiv_is_zero {el:F} {kl : F → Option Unit} (er:Exp F F) (kr:F -> Circuit F F)
  (he : el = Exp.eval er)
  (hk : ∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) :
  Simulation.s_bisim (bind ((is_zero el)) kl) (Circuit.eval (.is_zero er kr)) := by
  aesop (add simp [Circuit.eval, bind, share, is_zero])

lemma equiv_accept :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil) := by
  constructor

def extract_manual₁ :
  { c:Circuit F F // Simulation.s_bisim (ex₁ (F := F)) c.eval } := by
  unfold ex₁
  refine ⟨?c,?p⟩
  case' p =>
    apply circuit_ext (h := Simulation.s_bisim.lam (fun _ ↦ ?rest))
  case rest =>
    apply equiv_accept
  rfl

def extract_manual₃ :
  { c:Circuit F F // Simulation.s_bisim (ex₃ (F := F)) c.eval } := by
  unfold ex₃
  refine ⟨?c,?p⟩
  swap
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_right 2
  apply equiv_eq0 (er := Exp.c _) (he := rfl)
  apply equiv_share (er := Exp.v _) (h := rfl) (h₁ := fun _ ↦ ?_)
  swap
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_accept
  swap
  rfl

def extract_manual₄ :
  { c:Circuit F F // Simulation.s_bisim (ex₄ (F := F)) c.eval } := by
  unfold ex₄
  refine ⟨?c,?p⟩
  swap
  apply circuit_ext (h := Simulation.s_bisim.lam fun X ↦ ?rest)
  rotate_right 2
  apply equiv_is_zero (er := Exp.c _) (he := rfl)
  intros x
  apply equiv_eq0 (er := Exp.c _) (he := rfl)
  apply equiv_accept
  swap
  rfl

def extract_manual₆ :
  { c:Circuit F F // Simulation.s_bisim (
    (ex₆ (F := F))
  ) c.eval } := by
  unfold ex₆
  refine ⟨?c,?p⟩
  swap
  dsimp -zeta only [curry]
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_right 2
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_right 5
  apply equiv_eq0 (er := Exp.c _) (he := rfl)
  apply equiv_share (er := Exp.v _) (h := rfl) (h₁ := fun _ ↦ ?_)
  swap
  apply equiv_eq0 (er := Exp.c _) (he := rfl)
  apply equiv_accept
  swap
  rfl
  swap
  rfl

def extract_manual₇ :
  { c:Circuit F F // Simulation.s_bisim (ex₇ (F := F)) c.eval } := by
  unfold ex₇
  refine ⟨?c,?p⟩
  swap
  dsimp -zeta only [curry]
  
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_right 2
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_right 5
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_right 8
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  dsimp
  apply equiv_eq0 (er := Exp.c _) (he := rfl)
  apply equiv_accept
  any_goals rfl

#print extract_manual₇

def extract_automatic₁ :
  { c:Circuit F F // Simulation.s_bisim (ex₁ (F := F)) c.eval } := by
  extract using ex₁

def extract_automatic₂ :
  { c:Circuit F F // Simulation.s_bisim (ex₂ (F := F)) c.eval } := by
  extract using ex₂

def extract_automatic₃ :
  { c:Circuit F F // Simulation.s_bisim (ex₃ (F := F)) c.eval } := by
  extract using ex₃

def extract_automatic₄ :
  { c:Circuit F F // Simulation.s_bisim (ex₄ (F := F)) c.eval } := by
  extract using ex₄

def extract_automatic₅ :
  { c:Circuit F F // Simulation.s_bisim (ex₅ (F := F)) c.eval } := by
  extract using ex₅

def extract_automatic₆ :
  { c:Circuit F F // Simulation.s_bisim (ex₆ (F := F)) c.eval } := by
  extract using ex₆

def extract_automatic₇ :
  { c:Circuit F F // Simulation.s_bisim (ex₇ (F := F)) c.eval } := by
  extract using ex₇

def WW {a : ℕ} (b : Fin a) {c : ℕ} (d : Fin c) : Option Unit := sorry

#print extract_automatic₁
#print extract_automatic₂
#print extract_automatic₃
#print extract_automatic₄
#print extract_automatic₅
#print extract_automatic₆

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
  apply equiv_accept
  swap
  rfl

end EXAMPLES

end Clap
