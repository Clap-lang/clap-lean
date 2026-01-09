import Mathlib.Data.ZMod.Basic

import Clap.Circuit
import Clap.Simulation

namespace Clap

variable {p : ℕ} [Fact (Nat.Prime p)]

namespace Spec

def eq0 (e : ZMod p) : Option Unit :=
  if e = 0 then some () else none

def share (e : ZMod p) : ZMod p := e

def is_zero (e : ZMod p) : ZMod p := if e = 0 then 1 else 0

def assert_range (w : ℕ) (e : ZMod p) : Option Unit := if e.val < 2^w then some () else none

def div_rem (e:ZMod p) : Option (ZMod p × ZMod p) :=
  let d := e / (2^8)
  let r := e % (2^8)
  (d,r)

def accept : Unit -> Unit := fun () => ()

/-
  Expand a function that takes a vector of n Felts, into a series of n
  functions taking a single Felt.
  e.g. Vector F 2 -> Option Unit  ~>  F -> F -> Option Unit
-/
@[reducible]
def typ (a r : Type) : ℕ -> Type
  | 0   => r
  | n+1 => a -> typ a r n

@[reducible]
def curry {a r : Type} (n : ℕ) (k : Vector a n -> r) : typ a r n :=
  match n with
  | 0 => k ⟨#[], by rfl⟩
  | n+1 => fun (x : a) => curry n (fun l => k (Vector.push l x))

#guard curry 2 (fun x => x[0] == 0 && x[1] == 1) 1 0 = True

lemma equiv_eq0 (el : ZMod p) (er : Exp (ZMod p) (ZMod p)) (cl : Option Unit) (cr : Circuit p (ZMod p)) :
    el = Exp.eval er ->
    Simulation.s_bisim cl (Circuit.eval cr) ->
    Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  intro he hc
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

lemma equiv_share (el : ZMod p) (er : Exp (ZMod p) (ZMod p)) (kl : ZMod p -> Option Unit) (kr : ZMod p -> Circuit p (ZMod p)) :
  el = Exp.eval er ->
  (∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) ->
  Simulation.s_bisim (bind (share el) kl) (Circuit.eval (.share er kr)) := by
  intro he hk
  simp only [Circuit.eval,bind,share]
  rw [he]
  apply hk

lemma equiv_assert_range (el : ZMod p) (er : Exp (ZMod p) (ZMod p)) (cl : Option Unit) (cr : Circuit p (ZMod p)) (w : ℕ)
  (he : el = Exp.eval er)
  (hc : Simulation.s_bisim cl (Circuit.eval cr)) :
  Simulation.s_bisim (Option.bind (assert_range w el) (fun () => cl)) (Circuit.eval (.assert_range w er cr)) := by
  simp only [Circuit.eval,Option.bind,assert_range]
  split
  split
  case _ _ heq her =>
    simp at heq
    rw [he] at heq
    grind
  case _ _ hel her =>
    constructor
  case _ _ _ hel =>
    simp at hel
    rw [he] at hel
    simp
    split
    . apply hc
    . contradiction

end Spec

namespace Example_base

open Spec

/-
  A circuit is a function from any number of arguments of type F or Vector F to Option Unit.
-/

def ex p (i: ZMod p) : Option Unit := do
  eq0 i
  let vi <- share i
  eq0 (vi + i)
  assert_range 2 vi
  accept ()

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  .lam (fun i =>
  .eq0 (.v i) (
  .share (.v i) (fun vi =>
  .eq0 (.v vi + .v i) (
  .assert_range 2 (.v vi) (
  .nil)))))

theorem equiv :
  Simulation.s_bisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
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
    apply equiv_assert_range
    constructor
    constructor

theorem extract :
  ∃ c : Circuit p (ZMod p), Simulation.s_bisim (ex p) (Circuit.eval c) := by
  unfold ex
  simp only [bind]
  refine ⟨?c,?p⟩
  case p =>
--  apply Simulation.s_bisim.lam (F:=(ZMod p)) (fun x => ?kl) (fun x => (Circuit.eval ?kr))
    sorry
  sorry

end Example_base

namespace Example_vec

open Spec

def ex p (is : Vector (ZMod p) 2) : Option Unit := do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  accept ()

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  Circuit.curry 2 (fun is =>
  .eq0 (.v is[0]) (
  .share (.v is[0]) (fun vi =>
  .eq0 (.v vi + .v is[1]) (
  .nil))))

theorem equiv :
  Simulation.s_bisim (curry 2 (ex p)) (Circuit.eval' (ex_circuit_fun p)) := by
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
def ex p (xs ys zs: Vector (ZMod p) 2) : Option Unit :=
-/
def ex p :=
  curry 2 (fun (xs: Vector (ZMod p) 2) =>
  curry 2 (fun (ys: Vector (ZMod p) 2) =>
  curry 2 (fun (zs: Vector (ZMod p) 2) => do
  let xys := Vector.map (fun ((x,y): ZMod p × ZMod p) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept ()
  )))

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  Circuit.curry 2 (fun xs =>
  Circuit.curry 2 (fun ys =>
  Circuit.curry 2 (fun zs =>
  .eq0 ((.v xs[0]) + (.v ys[0]) - (.v zs[0])) (
  .eq0 ((.v xs[1]) + (.v ys[1]) - (.v zs[1])) (
  .nil)))))

theorem equiv :
    Simulation.s_bisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [curry]
  simp only [Circuit.curry]
  repeat (constructor ; intro)
  dsimp
  -- protect rhs, reduce lhs and but the binds in the right shape
  generalize h : @Circuit.eq0 p _ _ _ = rhs
  simp!
  rw [<-h]
  repeat (rw [Option.bind_assoc])
  apply equiv_eq0
  simp [Vector.append, Exp.eval]
  -- protect rhs, reduce lhs and but the binds in the right shape
  generalize h : @Circuit.eq0 p _ _ _ = rhs
  simp!
  rw [<-h]
  repeat (rw [Option.bind_assoc])
  apply equiv_eq0
  . simp [Vector.append, Exp.eval]
  . simp!
    constructor

end Example_fold

end Clap
