import Lean
import Qq

import Clap.Simulation
import Clap.Spec

open Lean Qq

namespace Clap

variable {p : ℕ} [Fact (Nat.Prime p)]

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

def isBindBind (lhs : Expr) : MetaM Bool := do
  let (`Bind.bind, ⟨_ :: _ :: _ :: _ :: f :: _⟩) := lhs.getAppFnArgs
    | return false
  return f.isAppOf `Bind.bind

-- elab "isBindBind" : tactic => do
--   let goal ← Elab.Tactic.getMainGoal
--   -- logInfo m!"type: {←goal.getType'}"
--   logInfo m!"isBindBind: {←isBindBind (←lhsOfBisim (←goal.getType'))}"

set_option hygiene false in -- We'll see about this one, tired of `mkIdent` :).
/--
Use `lhs` for granular control over matching if needed.
-/
def step (goals : Goals) : MetaM Goals := do
  let lhs ← lhsOfBisim (←goals.inference.get!.getType')
  if ←isBindBind lhs
  then goals.runTactic (←`(tacticSeq|rw [bind_assoc]
                                     try (rw [Option.bind_eq_bind, Option.bind_some])))
  else goals.seqTacs <|
         -- TODO(workaround) We want to synthesise this list automatically.
         [
           (←`(tactic|unfold add_carry))
         ] ++
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
                               (hk := fun _ ↦ ?_))),
           (←`(tactic|apply $(mkIdent `Spec.equiv_assert_range)
                               (er := Exp.c _)
                               (he := rfl))),
           (←`(tactic|apply $(mkIdent `equiv_div_rem)
                               (er := Exp.c _)
                               (he := rfl)
                               (hc := fun _ ↦ ?_)))
         ]

def extractTac (inferenceGoal : MVarId) : MetaM Goals := do
  let mut goals ← curry inferenceGoal
  -- let mut i := 0
  while true do
    match goals.inference with
    | .none => break
    | .some inference => goals ← Goals.unassignedGoals =<<
                                   step goals 
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

lemma circuit_ext {α : Type} {f : ZMod p → α} {g : ZMod p → Circuitₑ p} {g' : Circuitₑ p}
  (h : Simulation.s_bisim f (Circuit.eval (Circuit.lam g)))
  (hint : g' = Circuit.lam g) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

lemma equiv_share {el : ZMod p} {er : Expₑ p} {kl : ZMod p → Option Unit} {kr : ZMod p -> Circuitₑ p}
  (h : el = Exp.eval er)
  (h₁ : ∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) :
  Simulation.s_bisim (bind (Spec.share el) kl) (Circuit.eval (.share er kr)) := by
  unfold Spec.share
  aesop

@[reducible]
def typ (a r:Type) : Nat -> Type
  | 0   => r
  | n+1 => a -> typ a r n

@[reducible]
def curry {α β : Type} (n : Nat) (k : Vector α n → β) : typ α β n :=
  match n with
  | 0 => k #v[]
  | n + 1 => fun x => curry n fun l => k ⟨⟨x :: l.toList⟩, by simp⟩

/--
TODO(unused)
-/
private def _explode (name : Name) (len : Nat) : String :=
  String.intercalate " " <| List.range len |>.map fun i ↦ s!"{name}[{i}]"

def curry! (circuit : Name) : MetaM Unit := do
  let .some decl := (← getEnv).find? circuit | throwError m!"Undeclared constant: {circuit}"
  let t := decl.type
  logInfo m!"t: {t} val: {decl.value!}"
  let stuff : MetaM _ := Meta.lambdaTelescope decl.value! fun args ret ↦ do
    logInfo m!"args: {args}"
    logInfo m!"ret: {ret}"
    for arg in args do
      logInfo m!"{arg} is {if (←arg.fvarId!.getDecl).binderInfo == .default then "explicit" else "implicit"}"
    return args
  where 

abbrev FU8 p := ZMod p

def FU8.mk (x : FU8 p) : Option Unit := Spec.assert_range 8 x

abbrev FB p := ZMod p

@[irreducible]
def div_rem (e : ZMod p) : Option (ZMod p × ZMod p) :=
  let d : Nat := e.val / 256
  let r : Nat := e.val % 256
  pure (d, r)

@[irreducible]
def add_carry (a b : FU8 p) (c : FB p := 0) : Option (FU8 p × FB p) := do
  -- behaves well only of p>2^(8+1+1)
  let o : FU8 p ← a + b + c
  let (d, r) ← div_rem o
  (r, d)

open Spec

-- TODO - Change the example :).
def ex (a b : FU8 p) : Option Unit := do
  FU8.mk a
  FU8.mk b
  let oXc' ← add_carry a b -- do {...}
  eq0 (a + b - oXc'.2 * 256 + oXc'.1)
  accept ()

def ex₁ (i : ZMod p) : Option Unit := do
  accept ()

def ex₂ (i: ZMod p) : Option Unit := do
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

def ex₃ (i : ZMod p) : Option Unit := do
  eq0 i
  let vi ← share i
  eq0 (vi + i)
  accept ()

-- This is (eq0 i); baby steps.
def ex₄ (i : ZMod p) : Option Unit := do
  let x ← is_zero i
  eq0 (1 - x)
  accept ()

def ex₅ (is₁ : ZMod p) (is₂ : ZMod p) : Option Unit := do
  eq0 is₁
  let vi <- share is₁
  eq0 (vi + is₂)
  accept ()

def ex₆ :=
  curry 2 (fun (is : Vector (ZMod p) 2) ↦ do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  return accept ())

def ex₇ :=
  curry 2 (fun (xs: Vector (ZMod p) 2) =>
  curry 2 (fun (ys: Vector (ZMod p) 2) =>
  curry 2 (fun (zs: Vector (ZMod p) 2) => do
  eq0 (xs[0]-zs[1])
  eq0 (xs[1]-zs[0])
  eq0 (ys[0]-zs[0])
  eq0 (ys[1]-xs[1])
  return accept ()
  )))

def ex₇' (xs ys zs : Vector (ZMod p) 2) := do
  eq0 (xs[0]-zs[1])
  eq0 (xs[1]-zs[0])
  eq0 (ys[0]-zs[0])
  eq0 (ys[1]-xs[1])
  return accept ()
  
example {xs ys zs : Vector (ZMod p) 2} : ex₇ xs[0] xs[1] ys[0] ys[1] zs[0] zs[1] = ex₇' xs ys zs := by rfl
  
  

-- def ex₇' (xs: Vector F 2) (ys: Vector F 2) (zs: Vector F 2) : typ F (typ F (typ F (Option Unit) 2) 2) 2 := _

-- example {is : Vector F 2} : ex₆ is = ex₅ is[0] is[1] := rfl

-- match first_line
--   | let _ ← isZero => ...
--   |

-- def ex_circuit : Circuit' (F p) := fun _ =>
--   .lam (fun i =>
--   .is_zero (.v i) (fun x ↦
--   .eq0 (1 - .v x)
--   .nil))

lemma equiv_eq0 {el : ZMod p} {er : Expₑ p} {cl : Option Unit} {cr : Circuitₑ p}
  (he: el = Exp.eval er)
  (hc: Simulation.s_bisim cl (Circuit.eval cr)) :
  Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  aesop (add unsafe 10% (by constructor)) (add simp eq0)

lemma equiv_is_zero {el : ZMod p} {kl : ZMod p → Option Unit} (er:Expₑ p) (kr:ZMod p -> Circuitₑ p)
  (he : el = Exp.eval er)
  (hk : ∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) :
  Simulation.s_bisim (bind (is_zero el) kl) (Circuit.eval (.is_zero er kr)) := by
  aesop (add simp [Circuit.eval, bind, share, is_zero])

lemma equiv_div_rem (el : ZMod p) (er : Expₑ p) (kl : ZMod p × ZMod p -> Option Unit) (kr : ZMod p × ZMod p -> Circuitₑ p)
  (he : el = Exp.eval er)
  (hc : ∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) :
  Simulation.s_bisim (bind (div_rem el) kl) (Circuit.eval (.div_rem er kr)) := by
  sorry

lemma equiv_accept :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (p := p) .nil) := by
  constructor

-- set_option pp.notation false in
def extract_manual :
  { c : Circuitₑ p // Simulation.s_bisim (ex (p := p)) c.eval } := by
  unfold ex  
  constructor
  unfold FU8.mk
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply Spec.equiv_assert_range (er := Exp.c _) (he := rfl)
  apply Spec.equiv_assert_range (er := Exp.c _) (he := rfl)
  dsimp -zeta only
  unfold add_carry
  rw [bind_assoc]
  rw [Option.bind_eq_bind]
  rw [Option.bind_some]
  rw [bind_assoc]
  apply equiv_div_rem (er := Exp.c _) (he := rfl) (hc := fun _ ↦ ?_)
  rotate_left 1
  rw [Option.bind_eq_bind]
  rw [Option.bind_some]
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_accept
  rotate_right 2
  rfl
  rotate_right 2
  rfl

def extract_automatic :
  { c : Circuitₑ p // Simulation.s_bisim (ex (p := p)) c.eval } := by
  extract using ex

#print extract_automatic

-- first | repeat high_prio | repeat low_prio | apply lem₁ | apply lem₂

set_option pp.notation false in
def extract_manual' :
  { c : Circuitₑ p // Simulation.s_bisim (ex (p := p)) c.eval } := by
  unfold ex  
  constructor
  unfold add_carry
  unfold FU8.mk
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
  rotate_left 3
  apply Spec.equiv_assert_range (er := Exp.c _) (he := rfl)
  apply Spec.equiv_assert_range (er := Exp.c _) (he := rfl)
  dsimp -zeta only
  rw [bind_assoc]
  rw [Option.bind_eq_bind]
  rw [Option.bind_some]
  rw [bind_assoc]
  apply Spec.equiv_div_rem (er := Exp.c _) (he := rfl) (hc := fun _ ↦ ?_)
  rotate_left 1
  rw [Option.bind_eq_bind]
  rw [Option.bind_some]
  apply equiv_eq0 (er:=Exp.c _) (he:=rfl)
  apply equiv_accept
  rotate_right 2
  rfl
  rotate_right 2
  rfl



  -- rw [Option.bind_eq_bind]
  -- rw [Option.bind_eq_bind]
  -- rw [Option.bind_eq_bind]
  -- rw [Option.bind_assoc]
  
  
  

-- lemma circuit_ext_vec {α : Type} {k} {f : Vector (ZMod p) k → α} {g : ZMod p → Circuitₑ p} {g' : Circuitₑ p}
--   (h : Simulation.s_bisim (curry k f) (Circuit.eval (Circuit.lam g)))
--   (hint : g' = Circuit.lam g) :
--   Simulation.s_bisim f (Circuit.eval g') := by
--   subst hint

def extract_manual₁ :
  { c:Circuitₑ p // Simulation.s_bisim (ex₁ (p := p)) c.eval } := by
  unfold ex₁
  refine ⟨?c,?p⟩
  case' p =>
    apply circuit_ext (h := Simulation.s_bisim.lam (fun _ ↦ ?rest))
  case rest =>
    apply equiv_accept
  rfl

def extract_manual₃ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₃ (p := p)) c.eval } := by
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
  { c : Circuitₑ p // Simulation.s_bisim (ex₄ (p := p)) c.eval } := by
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

-- def extract_manual₆ :
--   { c:Circuit F F // Simulation.s_bisim (
--     (ex₆ (F := F))
--   ) c.eval } := by
--   unfold ex₆
--   refine ⟨?c,?p⟩
--   swap
--   dsimp -zeta only [curry]
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_right 2
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_right 5
--   apply equiv_eq0 (er := Exp.c _) (he := rfl)
--   apply equiv_share (er := Exp.v _) (h := rfl) (h₁ := fun _ ↦ ?_)
--   swap
--   apply equiv_eq0 (er := Exp.c _) (he := rfl)
--   apply equiv_accept
--   swap
--   rfl
--   swap
--   rfl

-- def extract_manual₇ :
--   { c:Circuit F F // Simulation.s_bisim (ex₇ (F := F)) c.eval } := by
--   unfold ex₇
--   refine ⟨?c,?p⟩
--   swap
--   dsimp -zeta only [curry]
  
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_right 2
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_right 5
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_right 8
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   dsimp
--   apply equiv_eq0 (er := Exp.c _) (he := rfl)
--   apply equiv_accept
--   any_goals rfl

-- def extract_manual₇ :
--   { c : Circuitₑ p // Simulation.s_bisim (ex₇' (p := p)) c.eval } := by
--   unfold ex₇'
--   refine ⟨?c,?p⟩
--   swap
--   apply circuit_ext_vec
--   dsimp -zeta only [curry]
--   dsimp
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_right 8
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   apply circuit_ext (h := Simulation.s_bisim.lam fun _ ↦ ?_)
--   rotate_left 3
--   dsimp
--   apply equiv_eq0 (er := Exp.c _) (he := rfl)
--   apply equiv_accept
--   any_goals rfl

-- #print extract_manual₇

def extract_automatic₁ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₁ (p := p)) c.eval } := by
  extract using ex₁

def extract_automatic₂ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₂ (p := p)) c.eval } := by
  extract using ex₂

def extract_automatic₃ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₃ (p := p)) c.eval } := by
  extract using ex₃

def extract_automatic₄ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₄ (p := p)) c.eval } := by
  extract using ex₄

def extract_automatic₅ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₅ (p := p)) c.eval } := by
  extract using ex₅

def extract_automatic₆ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₆ (p := p)) c.eval } := by
  extract using ex₆

def extract_automatic₇ :
  { c : Circuitₑ p // Simulation.s_bisim (ex₇ (p := p)) c.eval } := by
  extract using ex₇

-- def WW {a : ℕ} (b : Fin a) {c : ℕ} (d : Fin c) : Option Unit := sorry

#print extract_automatic₁
#print extract_automatic₂
#print extract_automatic₃
#print extract_automatic₄
#print extract_automatic₅
#print extract_automatic₆
#print extract_automatic₇

def extract_manual'' :
  { c : Circuitₑ p // Simulation.s_bisim (ex₂ (p := p)) c.eval } := by
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
