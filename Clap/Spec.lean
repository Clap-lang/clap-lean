import Mathlib.Data.ZMod.Basic

import Clap.Circuit
import Clap.Simulation

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
def assert_range (w : ℕ) (e : ZMod p) : Option Unit := if e.val < 2^w then .some () else .none

@[irreducible]
def div_rem (e:ZMod p) : Option (ZMod p × ZMod p) :=
  let d : ℕ := e.val / 256
  let r : ℕ := e.val % 256
  .some (d, r)

def succ (i : UInt8) : UInt8 := i + 1

abbrev FU8 (p:ℕ) : Type := {f : ZMod p | f.val < 2^8}

def coe_fu8_uint8 (f:FU8 p) : UInt8 :=
  if p > 256 then UInt8.ofNat f.val.val else 0

instance coe : CoeOut (FU8 p) UInt8 where
  coe := coe_fu8_uint8

namespace FU8

def add (a b : ZMod p) : Option (ZMod p) := do
  let o := a + b
  assert_range 8 o
  o

end FU8
lemma f_add_no_overflow_generic {a b : ZMod p}
  (h₁ : a.val < p / 2) (h₂ : b.val < p / 2) : (a + b).val = a.val + b.val := by
  grind [ZMod.val_add_of_lt]

--TODO maybe this should start with nat and apply convertions?omit [Fact (Nat.Prime p)] in
lemma fu8_add_no_overflow {a b : FU8 p}
  (h₁ : 256 < p) (h₂ : a.val.val + b.val.val < 256) :
  (a.val + b.val).val = a.val.val + b.val.val := by
  grind [ZMod.val_add_of_lt]

def succ_c (i : ZMod p) : Option (ZMod p) := do
  let o : ZMod p := i.val + 1
  assert_range 8 o
  o

/-
  Expand a function that takes a vector of n Felts, into a series of n
  functions taking a single Felt.
  e.g. Vector F 2 -> Option Unit  ~>  F -> F -> Option Unit
-/
@[reducible]
def typ (a r : Type) : Nat → Type
  | 0     => r
  | n + 1 => a → typ a r n

@[reducible]
def curry {α β : Type} {n : Nat} (k : Vector α n → β) : typ α β n :=
  match n with
  | 0     => k #v[]
  | n + 1 => fun x => curry fun l => k ⟨⟨x :: l.toList⟩, by simp⟩

namespace Compiler

section

open scoped Simulation

variable {el : ZMod p} {er : Expₑ p}

@[aesop safe apply]
lemma equiv_lam {α : Type} {f : ZMod p → α} {g : ZMod p → Circuitₑ p}
  (cont : ∀ (x), f x ~ₛ ((g x)).eval) :
  f ~ₛ (Circuit.lam g).eval := Simulation.sBisim.lam cont

@[aesop safe apply]
lemma equiv_eq0 {cl : Option Unit} {cr : Circuitₑ p}
  (cont : cl ~ₛ cr.eval)
  (h : el = Exp.eval er) :
  (do eq0 el; cl) ~ₛ (Circuit.eq0 er cr).eval := by
  aesop (add simp eq0)

@[aesop safe apply]
lemma equiv_share {kl : ZMod p → Option Unit} {kr : ZMod p → Circuitₑ p}
  (cont : ∀ {x}, kl x ~ₛ (kr x).eval)
  (h : el = Exp.eval er) :
  (share el >>= kl) ~ₛ (Circuit.share er kr).eval := by
  aesop (add simp share)

@[aesop safe apply]
lemma equiv_assert_range {cl : Option Unit} {cr : Circuitₑ p} {w : ℕ}
  (cont : cl ~ₛ cr.eval)
  (h₁ : el = Exp.eval er) :
  (do assert_range w el; cl) ~ₛ (Circuit.assert_range w er cr).eval := by
  aesop (add simp assert_range)

@[aesop safe apply]
lemma equiv_accept : some accept ~ₛ (Circuit.nil (p := p)).eval := by
  constructor

end

end Compiler

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
  accept

#guard ex 7 0 = some ()
#guard ex 7 1 = none

-- def ex_unfolded : F -> Option Unit :=
--   fun i =>
--   bind (eq0 F i) (fun () =>
--   bind (share F i) (fun vi =>
--   bind (eq0 F (vi + i)) (fun () =>
--   some ())))

def ex_circuit_fun (p : ℕ) (var : Type) : Circuit p var :=
  .lam (fun i =>
  .eq0 (.v i) (
  .share (.v i) (fun vi =>
  .eq0 (.v vi + .v i) (
  .assert_range 2 (.v vi) (
  .nil)))))

theorem equiv :
  Simulation.sBisim (ex p) ((ex_circuit_fun p (ZMod p)).eval) := by
  unfold ex_circuit_fun
  unfold ex
  apply Compiler.equiv_lam fun _ ↦ ?_
  apply Compiler.equiv_eq0
  apply Compiler.equiv_share
  intros
  apply Compiler.equiv_eq0
  apply Compiler.equiv_assert_range
  apply Compiler.equiv_accept
  all_goals try rfl

end Example_base

namespace Example_vec

open Spec

def ex p (is : Vector (ZMod p) 2) : Option Unit := do
  eq0 is[0]
  let vi ← share is[0]
  eq0 (vi + is[1])
  accept

def ex_circuit_fun (p : ℕ) : Circuitₑ p  :=
  .lam fun x ↦ .lam fun y ↦
  .eq0 (.v x) (
  .share (.v x) fun vi =>
  .eq0 (.v vi + .v y) (
  .nil))

theorem equiv :
  Simulation.sBisim (curry (n := 2) (ex p)) ((ex_circuit_fun p).eval) := by
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

def ex_circuit_fun (p : ℕ) : Circuitₑ p :=
  .lam fun x1 ↦ .lam fun x2 ↦ .lam fun x3 ↦ .lam fun x4 ↦ .lam fun x5 ↦ .lam fun x6 ↦ 
  .eq0 ((.v x1) + (.v x3) - (.v x5)) (
  .eq0 ((.v x2) + (.v x4) - (.v x6)) (
  .nil))

theorem equiv :
    Simulation.sBisim (ex p) (Circuit.eval (ex_circuit_fun p)) := by
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
