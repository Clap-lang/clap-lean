import Clap.Circuit
import Clap.Simulation

namespace Clap

namespace Spec

--variable (F var:Type) [Field F] [DecidableEq F]
variable (p:ℕ) [Fact (Nat.Prime p)]
abbrev F : Type := ZMod p

def eq0 {p} (e:F p) : Option Unit :=
  if e = 0 then some () else none

def share {p} (e:F p) : F p := e

def is_zero {p} (e:F p) : F p := if e = 0 then 1 else 0

def assert_range {p} (w:ℕ) (e:F p) : Option Unit := if e.val < 2^w then some () else none

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

lemma equiv_eq0 : ∀ p [Fact (Nat.Prime p)] [Coe (F p) Nat] (el:F p) (er:Exp (F p) (F p)) (cl:Option Unit) (cr:Circuit (F p) (F p)),
  el = Exp.eval er ->
  Simulation.s_bisim cl (Circuit.eval cr) ->
  Simulation.s_bisim (Option.bind (eq0 el) (fun () => cl)) (Circuit.eval (.eq0 er cr)) := by
  intro p _ _ el er cl cr he hc
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

lemma equiv_share : ∀ p [Fact (Nat.Prime p)] [Coe (F p) Nat] (el:F p) (er:Exp (F p) (F p)) (kl:F p -> Option Unit) (kr:F p -> Circuit (F p) (F p)),
  el = Exp.eval er ->
  (∀ x, Simulation.s_bisim (kl x) (Circuit.eval (kr x))) ->
  Simulation.s_bisim (bind (share el) kl) (Circuit.eval (.share er kr)) := by
  intro p _ _ el er kl kr he hk
  simp only [Circuit.eval,bind,share]
  rw [he]
  apply hk

end Spec

namespace Example_base

open Spec

/-
  A circuit is a function from any number of arguments of type F or Vector F to Option Unit.
-/

def ex p (i: F p) : Option Unit := do
  eq0 i
  let vi <- share i
  eq0 (vi + i)
  accept ()

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

def ex_circuit_fun p : Circuit' (F p) := fun _ =>
  .lam (fun i =>
  .eq0 (.v i) (
  .share (.v i) (fun vi =>
  .eq0 (.v vi + .v i) (
  .nil))))

theorem equiv : ∀ p [Fact (Nat.Prime p)] [Coe (F p) Nat],
  Simulation.s_bisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  intro p _ _
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

theorem extract : ∀ p [Fact (Nat.Prime p)] [Coe (F p) Nat],
  ∃ c:Circuit (F p) (F p), Simulation.s_bisim (ex p) (Circuit.eval c) := by
  intro p _ _
  unfold ex
  simp only [bind]
  refine ⟨?c,?p⟩
  case p =>
--  apply Simulation.s_bisim.lam (F:=(F p)) (fun x => ?kl) (fun x => (Circuit.eval ?kr))
    sorry
  sorry

end Example_base

namespace Example_vec

open Spec

def ex p (is: Vector (F p) 2) : Option Unit := do
  eq0 is[0]
  let vi <- share is[0]
  eq0 (vi + is[1])
  accept ()

def ex_circuit_fun p : Circuit' (F p) := fun _ =>
  Circuit.curry 2 (fun is =>
  .eq0 (.v is[0]) (
  .share (.v is[0]) (fun vi =>
  .eq0 (.v vi + .v is[1]) (
  .nil))))

theorem equiv : ∀ p [Fact (Nat.Prime p)] [Coe (F p) Nat],
  Simulation.s_bisim (curry 2 (ex p)) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [bind]
  simp only [Circuit.eval']
  intro p _ _
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
def ex p (xs ys zs: Vector (F p) 2) : Option Unit :=
-/
def ex p :=
  curry 2 (fun (xs: Vector (F p) 2) =>
  curry 2 (fun (ys: Vector (F p) 2) =>
  curry 2 (fun (zs: Vector (F p) 2) => do
  let xys := Vector.map (fun ((x,y): F p × F p) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept ()
  )))

def ex_circuit_fun p : Circuit' (F p) := fun _ =>
  Circuit.curry 2 (fun xs =>
  Circuit.curry 2 (fun ys =>
  Circuit.curry 2 (fun zs =>
  .eq0 ((.v xs[0]) + (.v ys[0]) - (.v zs[0])) (
  .eq0 ((.v xs[1]) + (.v ys[1]) - (.v zs[1])) (
  .nil)))))

set_option pp.parens true

theorem equiv : ∀ p [Fact (Nat.Prime p)] [Coe (F p) Nat],
  Simulation.s_bisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  intro p _ _
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

end Clap
