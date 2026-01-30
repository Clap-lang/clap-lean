import Mathlib.FieldTheory.Finite.Basic -- field operations

import Clap.Primes
import Clap.Circuit
import Clap.Simulation
import Clap.Wheels

namespace Clap

variable {p : ℕ}

namespace Spec

@[irreducible]
def accept : Unit := ()

@[irreducible]
def eq0 (e : ZMod p) : Option Unit := if e = 0 then .some () else .none

@[irreducible]
def share (e : ZMod p) : Option (ZMod p) := e

@[irreducible]
def is_zero (e : ZMod p) : Option (ZMod p) := if e = 0 then .some 1 else .some 0

@[irreducible]
def num2bits [Fact (Nat.Prime p)] (w : ℕ) (e : ZMod p) : Option (List (ZMod p)) :=
  if e.val < 2^w then .some (num2bits_pure w e) else .none

def assert_range [Fact (Nat.Prime p)] (w : ℕ) (e : ZMod p) : Option Unit := do
  let _ <- num2bits w e ; ()

namespace Compiler

section

open scoped Simulation

variable {el : ZMod p} {er : Expₑ p} [Fact (Nat.Prime p)]

@[aesop safe apply]
lemma equiv_lam {α : Type} {f : ZMod p → α} {g : ZMod p → Circuitₑ p}
  (cont : ∀ (x), f x ~ₛ ((g x)).eval) :
  f ~ₛ (Circuit.lam g).eval := Simulation.sBisim.lam cont

@[aesop safe apply]
lemma equiv_eq0 {cl : Option Unit} {cr : Circuitₑ p}
  (cont : cl ~ₛ cr.eval)
  (h : el = er.eval) :
  (do eq0 el; cl) ~ₛ (Circuit.eq0 er cr).eval := by
  aesop (add simp eq0)

@[aesop safe apply]
lemma equiv_share {kl : ZMod p → Option Unit} {kr : ZMod p → Circuitₑ p}
  (cont : ∀ (x), kl x ~ₛ (kr x).eval)
  (h : el = er.eval) :
  (share el >>= kl) ~ₛ (Circuit.share er kr).eval := by
  aesop (add simp share)

@[aesop safe apply]
lemma equiv_accept : some accept ~ₛ (Circuit.nil (p := p)).eval := by
  constructor

@[aesop safe apply]
lemma equiv_is_zero {el : ZMod p} {kl : ZMod p → Option Unit} {er : Expₑ p} {kr : ZMod p → Circuitₑ p}
  (cont : ∀ (x), kl x ~ₛ (kr x).eval)
  (h : el = er.eval) :
  Simulation.sBisim (bind (is_zero el) kl) (Circuit.eval (.is_zero er kr)) := by
  aesop (add simp [Circuit.eval, bind, share, is_zero])

@[aesop safe apply]
lemma equiv_num2bits {kl : List (ZMod p) -> Option Unit} {kr : List (ZMod p) -> Circuitₑ p} {w:ℕ}
  (cont : ∀ x, kl x ~ₛ (kr x).eval)
  (h : el = Exp.eval er) :
  (num2bits w el >>= kl) ~ₛ (Circuit.num2bits w er kr).eval := by
  aesop (add simp num2bits)

end

end Compiler

end Spec

namespace Example_base

open Spec

/-
  A circuit is a function from any number of arguments of type F or Vector F to Option Unit.
-/

def ex [Fact (Nat.Prime p)] (i: ZMod p) : Option Unit := do
  eq0 i
  let vi <- share i
  eq0 (vi + i)
  let bs <- num2bits 2 vi
  eq0 bs[1]!
  accept

#guard ex (p:=7) 0 = some ()
#guard ex (p:=7) 1 = none

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

end Example_base

namespace Example_vec

open Spec

def ex p (is : Vector (ZMod p) 2) : Option Unit := do
  eq0 is[0]
  let vi ← share is[0]
  eq0 (vi + is[1])
  accept

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  .lam fun x ↦ .lam fun y ↦
  .eq0 (.v x) (
  .share (.v x) fun vi =>
  .eq0 (.v vi + .v y) (
  .nil))

theorem equiv [Fact (Nat.Prime p)] :
  Simulation.sBisim (curry (n := 2) (ex p)) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  dsimp only [curry]
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_eq0
  apply Compiler.equiv_share
  intros
  apply Compiler.equiv_eq0
  apply Compiler.equiv_accept
  rfl
  rfl
  rfl

end Example_vec

namespace Example_fold

open Spec

/- TODO these curry should disappear, the signature should be:
def ex p (xs ys zs: Vector (ZMod p) 2) : Option Unit :=
-/
def ex p :=
  curry (fun (xs: Vector (ZMod p) 2) =>
  curry (fun (ys: Vector (ZMod p) 2) =>
  curry (fun (zs: Vector (ZMod p) 2) => do
  let xys := Vector.map (fun ((x,y): ZMod p × ZMod p) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept
  )))

#guard ex 7 2 4 1 1 3 5 = some 90 -- [2,4] + [1,1] = [3,5]
#guard ex 7 2 4 1 1 3 6 = none

def ex_circuit_fun (p : ℕ) : Circuit' p := fun _ =>
  .lam fun x1 ↦ .lam fun x2 ↦ .lam fun x3 ↦ .lam fun x4 ↦ .lam fun x5 ↦ .lam fun x6 ↦
  .eq0 ((.v x1) + (.v x3) - (.v x5)) (
  .eq0 ((.v x2) + (.v x4) - (.v x6)) (
  .nil))

theorem equiv [Fact (Nat.Prime p)] :
    Simulation.sBisim (ex p) (Circuit.eval' (ex_circuit_fun p)) := by
  unfold ex_circuit_fun
  unfold ex
  simp only [curry]
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_lam fun _ ↦ ?_
  generalize h : @Circuit.eq0 p _ _ _ = rhs
  simp! [-Option.bind_eq_bind]; rw [←h]
  apply Compiler.equiv_eq0
  rw [Option.bind_eq_bind, Option.bind_some]; dsimp only
  rw [bind_assoc]
  apply Compiler.equiv_eq0
  simp
  apply Compiler.equiv_accept
  rfl
  rfl

end Example_fold

end Clap
