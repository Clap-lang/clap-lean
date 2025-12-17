import Clap.Circuit
import Clap.Simulation

set_option pp.parens true

namespace Clap

variable {F:Type} [Field F] [DecidableEq F]

namespace Spec

def eq0 (e:F) : Option Unit :=
  if e = 0 then some () else none

def share (e:F) : F := e

def is_zero (e:F) : F := if e = 0 then 1 else 0

-- def assert_range (w:ℕ) (e:F) : Option Unit := if e.val < 2^w then some () else none

def accept : Unit -> Unit := fun () => ()


/-
  Expand a function that takes a vector of n Felts, into a series of n
  functions taking a single Felt.
  e.g. Vector F 2 -> Option Unit  ~>  F -> F -> Option Unit
-/
@[reducible]
def typ (a r:Type) : ℕ -> Type
  | 0   => r
  | n+1 => a -> typ a r n

@[reducible]
def curry {a r:Type} (n:ℕ) (k:Vector a n -> r) : typ a r n :=
  match n with
  | 0 => k ⟨#[], by rfl⟩
  | n+1 => fun x:a => curry n (fun l => k (Vector.push l x) )

#guard curry 2 (fun x => x[0]==0 && x[1]==1) 1 0 = True

lemma equiv_eq0 : ∀ (el:F) (er:Exp F F) (cl:Option Unit) (cr:Circuit F F),
  el = Exp.eval er ->
  Simulation.s_bisim cl (Circuit.eval cr) ->
  Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  intro el er cl cr he hc
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

lemma equiv_share : ∀ (el:F) (er:Exp F F) (kl:F -> Option Unit) (kr:F -> Circuit F F),
  el = Exp.eval er ->
  (∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) ->
  Simulation.s_bisim (bind (share el) kl) (Circuit.eval (.share er kr)) := by
  intro el er kl kr he hk
  simp only [Circuit.eval,bind,share]
  rw [he]
  apply hk

lemma extract_lam {t} {s:F -> t} {k:F -> Circuit F F}
  (h:∀ x, Simulation.s_bisim (s x) (k x).eval) :
  Simulation.s_bisim s (Circuit.eval (.lam k)) := by
  constructor
  assumption

end Spec

namespace Example_base

open Spec

/-
  A circuit is a function from any number of arguments of type F or Vector F to Option Unit.
-/

def ex (i:F) : Option Unit := do
  eq0 i
  let vi <- share i
  eq0 (vi + i)
  accept ()

def id' {α} := id (α := α)

namespace Alt

section

variable [Repr F]

abbrev LogM := StateM String

def log (s : String) : LogM Unit := modify (·++s++"\n")

def LogM.run! (x : LogM Unit) : Std.Format :=
  x.run "" |>.run.2.toFormat
  
def eq0 (e:F) : LogM Unit := do
  log s!"eq0 {repr e}"
  return ()

def share (e:F) : LogM F := do
  log s!"share {repr e}"
  return e

def is_zero (e:F) : LogM F := do
  log s!"is_zero {repr e}"
  return if e == 0 then 1 else 0

def accept : Unit → LogM Unit := fun _ ↦ do
  log "nil"

def ex (i:F) : LogM Unit := do
  eq0 i
  let vi <- share i
  eq0 (vi + i)
  accept ()

#eval ex (2 : ZMod 3) |>.run!

def ex' :=
  curry 2 (fun (xs: Vector F 2) =>
  curry 2 (fun (ys: Vector F 2) =>
  curry 2 (fun (zs: Vector F 2) => do
  let xys := Vector.map (fun ((x,y): F × F) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept ()
  )))

#eval (@ex' (F := ZMod 3) _ _ 1 2 3 4 5 6  ).run "" |>.2.toFormat

  variable (a b : ZMod 3)

  def and! : ZMod 3 := a * b

  def or! : ZMod 3 := (a + b) - (a*b)

  def xor! : ZMod 3 := (a + b) - (2*a*b)

  def not! : ZMod 3 := (1 + a) - 2*a

def not (i o : ZMod 3) : LogM Unit := do
  log s!"{repr o} - not {repr i}"
  eq0 (o - (not! i))

def xor (a b o : ZMod 3) : LogM Unit := do
  modify (·++s!"{repr o} - xor {repr a} {repr b}\n")
  eq0 (o - (xor! a b))

def and (a b o : ZMod 3) : LogM Unit := do
  modify (·++s!"{repr o} - and {repr a} {repr b}\n")
  eq0 (o - (and! a b))

def or (a b o : ZMod 3) : LogM Unit := do
  modify (·++s!"{repr o} - and {repr a} {repr b}\n")
  eq0 (o - (or! a b))

-- MultiAND
-- TODO: DOUBLE CHECK THIS
def mAND (n : ℕ) {h : 2 ≤ n} (i : Vector (ZMod 3) n) (o : ZMod 3) : LogM Unit :=
  match n with
  | 2 => and i[0] i[1] o
  | n' + 3 => mAND_aux (n' + 3 - 2) (i.drop 2) (and! i[0] i[1]) o (h := by simp)
where
  mAND_aux (n : ℕ) {h : 1 ≤ n} (i : Vector (ZMod 3) n) (acc : ZMod 3) (o : ZMod 3) : LogM Unit :=
  match n with
  | 1 => do
    let tmp ← share (i[0] * acc)
    and i[0] acc tmp
    eq0 (o - tmp)
  | n' + 2 => do
    let tmp ← share (i[0] * acc)
    and i[0] acc tmp
    mAND_aux (n' + 1) (i.drop 1) tmp o (h := by simp)

#eval (mAND 5 (h := by simp) (i := #v[1, 2, 3, 4, 5]) (4)).run!

end

end Alt

example {a : F} : ex' (F := F) a = sorry := by
  unfold ex'
  unfold bind
  unfold_projs
  simp -beta only
  -- unfold liftM monadLift instMonadLiftTOfMonadLift Monad.
  simp -beta only

  dsimp
  repeat rw [Option.bind_assoc]
  unfold Option.bind
  simp!
  split; sorry

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

def ex_circuit_fun : Circuit' F := fun _ =>
  .lam (fun i =>
  .eq0 (.v i) (
  .share (.v i) (fun vi =>
  .eq0 (.v vi + .v i) (
  .nil))))

theorem equiv :
  Simulation.s_bisim (ex (F:=F)) (Circuit.eval' (ex_circuit_fun (F:=F))) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  constructor
  intro
  apply equiv_eq0
  simp [Exp.eval]
  apply equiv_share
  . simp [Exp.eval]
  . intro
    apply equiv_eq0
    simp [Exp.eval]
    constructor

end Example_base

namespace Example_vec

open Spec

def ex (is: Vector F 2) : Option Unit := do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  accept ()

def ex_circuit_fun : Circuit' F := fun _ =>
  Circuit.curry 2 (fun is =>
  .eq0 (.v is[0]) (
  .share (.v is[0]) (fun vi =>
  .eq0 (.v vi + .v is[1]) (
  .nil))))

theorem equiv :
  Simulation.s_bisim (curry 2 (ex (F:=F))) (Circuit.eval' (ex_circuit_fun (F:=F))) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  simp only [curry]
  simp only [Circuit.curry]
  repeat (constructor ; intro)
  apply equiv_eq0
  simp [Vector.append, Exp.eval]
  apply equiv_share
  . simp [Vector.append, Exp.eval]
  . intro
    apply equiv_eq0
    simp [Vector.append, Exp.eval]
    constructor

end Example_vec

namespace Example_fold

open Spec

/- TODO these curry should disappear, the signature should be:
def ex p (xs ys zs: Vector F 2) : Option Unit :=
-/
def ex :=
  curry 2 (fun (xs: Vector F 2) =>
  curry 2 (fun (ys: Vector F 2) =>
  curry 2 (fun (zs: Vector F 2) => do
  let xys := Vector.map (fun ((x,y): F × F) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept ()
  )))

def ex_circuit_fun : Circuit' F := fun _ =>
  Circuit.curry 2 (fun xs =>
  Circuit.curry 2 (fun ys =>
  Circuit.curry 2 (fun zs =>
  .eq0 ((.v xs[0]) + (.v ys[0]) - (.v zs[0])) (
  .eq0 ((.v xs[1]) + (.v ys[1]) - (.v zs[1])) (
  .nil)))))

example {a b c d e f} : ex (F := F) a b c d e f = sorry := by
  unfold ex
  simp!
  unfold Option.bind
  repeat rw [←Option.bind_assoc]
  simp!
  split; sorry
  
  rw [Option.bind_eq_some_iff.2 sorry]

theorem equiv :
  Simulation.s_bisim (ex (F:=F)) (Circuit.eval' (ex_circuit_fun (F:=F))) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [curry]
  simp only [Circuit.curry]
  repeat (constructor ; intro)
  dsimp
  -- protect rhs, reduce lhs and but the binds in the right shape
  generalize h:Circuit.eq0 _ _ = rhs
  simp!
  rw [<-h]
  repeat (rw [Option.bind_assoc])
  apply equiv_eq0
  simp [Vector.append, Exp.eval]
  -- protect rhs, reduce lhs and but the binds in the right shape
  generalize h:Circuit.eq0 _ _ = rhs
  simp!
  rw [<-h]
  repeat (rw [Option.bind_assoc])
  apply equiv_eq0
  . simp [Vector.append, Exp.eval]
  . simp!
    constructor

end Example_fold

namespace Example_extraction

open Spec

def ex (i: F) : Option Unit := do
--  eq0 i
  accept ()

lemma circuit_ext {α : Type} {f : F → α} {g : F → Circuit F F} {g' : Circuit F F}
  (hint : g' = Circuit.lam g)
  (h: Simulation.s_bisim f (Circuit.eval (Circuit.lam g))) :
  Simulation.s_bisim f (Circuit.eval g') := by grind

lemma abc :
  Simulation.s_bisim (some (accept ())) (Circuit.eval (F := F) .nil) := by
  constructor

def extract' :
  { c:Circuit F F // Simulation.s_bisim (ex (F := F)) c.eval } := by
  unfold ex
  refine ⟨?c,?p⟩
  -- iterate 2
  -- first
  case' p => -- case' does not enforce to close the goal
    apply circuit_ext (h := ?rest)
  case' c =>
    refine Circuit.lam fun _ ↦ ?y
  case' rest =>
    constructor
    intros x
    apply abc
  swap
  rfl

end Example_extraction

end Clap
