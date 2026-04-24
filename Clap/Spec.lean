import Clap.BitVec
import Clap.Circuit
import Clap.Simulation
import Clap.Wheels

namespace Clap

variable {p : ℕ}

namespace Spec.Compiler

@[irreducible]
def accept : Unit := ()

@[irreducible]
def eq0 (e : ZMod p) : Option Unit := if e = 0 then .some () else .none

@[irreducible]
def share (e : ZMod p) : Option (ZMod p) := some e

@[irreducible]
def isZero (e : ZMod p) : Option (ZMod p) := if e = 0 then some 1 else some 0

@[irreducible]
def num2bits (w : ℕ) (e : ZMod p) : Option (List (ZMod p)) :=
  if e.val < 2^w then .some (num2bitsLsbPure w e) else .none

/-- Bignum modular multiplication `(a · b) mod c`. Limbs are little-endian, each holding `w` bits, with `k` limbs per operand.
Returns `none` when any list has length `≠ k`, any limb does not fit in `w` bits, or the bignum value of `c` is 0. -/
@[irreducible]
def fpMul (w k : ℕ) (a b c : List (ZMod p)) : Option (List (ZMod p)) :=
  if a.length = k ∧ b.length = k ∧ c.length = k ∧ (∀ x ∈ a, x.val < 2^w) ∧ (∀ x ∈ b, x.val < 2^w) ∧ (∀ x ∈ c, x.val < 2^w)
  then
    let A : Nat := limbsToNat w a
    let B : Nat := limbsToNat w b
    let C : Nat := limbsToNat w c
    if C = 0 then none
    else some (natToLimbs w k ((A * B) % C))
  else none

export Clap (bits2num)

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
lemma equiv_isZero {el : ZMod p} {kl : ZMod p → Option Unit} {er : Expₑ p} {kr : ZMod p → Circuitₑ p}
  (cont : ∀ (x), kl x ~ₛ (kr x).eval)
  (h : el = er.eval) :
  Simulation.sBisim (bind (isZero el) kl) (Circuit.eval (.isZero er kr)) := by
  aesop (add simp [Circuit.eval, bind, share, isZero])

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

open Spec.Compiler

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

open Spec.Compiler

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
  apply equiv_lam fun _ ↦ ?_
  apply equiv_lam fun _ ↦ ?_
  apply equiv_eq0
  apply equiv_share
  intros
  apply equiv_eq0
  apply equiv_accept
  rfl
  rfl
  rfl

end Example_vec

namespace Example_fold

open Spec.Compiler

/- TODO these curry should disappear, the signature should be:
def ex p (xs ys zs: Vector (ZMod p) 2) : Option Unit :=
-/
def ex p :=
  curry (fun (xs: Vector (ZMod p) 2) =>
  curry (fun (ys: Vector (ZMod p) 2) =>
  curry (fun (zs: Vector (ZMod p) 2) => (do
  let xys := Vector.map (fun ((x,y): ZMod p × ZMod p) => x+y) (Vector.zip xs ys)
  for (xy,z) in Vector.zip xys zs do
    eq0 (xy-z)
  return accept : Option Unit)
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
  apply equiv_lam fun _ ↦ ?_
  apply equiv_lam fun _ ↦ ?_
  apply equiv_lam fun _ ↦ ?_
  apply equiv_lam fun _ ↦ ?_
  apply equiv_lam fun _ ↦ ?_
  apply equiv_lam fun _ ↦ ?_
  generalize h : @Circuit.eq0 p _ _ _ = rhs
  simp! [-Option.bind_eq_bind]; rw [←h]
  apply equiv_eq0
  rw [Option.bind_eq_bind, Option.bind_some]; dsimp only
  rw [bind_assoc]
  apply equiv_eq0
  simp
  apply equiv_accept
  rfl
  rfl

end Example_fold

end Clap

namespace TestFpMul

open Clap.Spec.Compiler

-- base 2^4 = 16, k = 2; 3 * 5 = 15, 15 mod 7 = 1, encoded LSB-first as [1, 0].
#guard fpMul (p := 17) 4 2 [3, 0] [5, 0] [7, 0] = some [1, 0]
-- zero operand: 0 * 5 mod 7 = 0.
#guard fpMul (p := 17) 4 2 [0, 0] [5, 0] [7, 0] = some [0, 0]
-- 2 * 3 mod 100 = 6. c = [4, 6] encodes 4 + 6·16 = 100; result 6 encodes as [6, 0].
#guard fpMul (p := 17) 4 2 [2, 0] [3, 0] [4, 6] = some [6, 0]
-- 15 * 15 mod 230 = 225, encoded as [1, 14] (1 + 14·16 = 225). c = [6, 14] encodes 6 + 14·16 = 230.
#guard fpMul (p := 17) 4 2 [15, 0] [15, 0] [6, 14] = some [1, 14]
-- 7 * 11 mod 13 = 77 mod 13 = 12.
#guard fpMul (p := 17) 4 1 [7] [11] [13] = some [12]
-- 100 * 50 mod 77 = 5000 mod 77 = 72. a = [4,6,0] = 100; b = [2,3,0] = 50; c = [13,4,0] = 77; 72 = [8,4,0].
#guard fpMul (p := 17) 4 3 [4, 6, 0] [2, 3, 0] [13, 4, 0] = some [8, 4, 0]
-- 12345 * 67890 mod 1_000_003 = 838_102_050 mod 1_000_003 = 99_536.
#guard fpMul (p := Primes.bn254) 64 1 [12345] [67890] [1000003] = some [99536]
-- B = 2^64, a = 5B + 100, b = 7B + 50, c = B² - 1.
-- (5B + 100)(7B + 50) = 35B² + 950B + 5000; modulo (B² - 1), 35B² ≡ 35, so
-- result = 5035 + 950B, encoded LSB-first as [5035, 950].
#guard fpMul (p := Primes.bn254) 64 2 [100, 5] [50, 7] [2^64 - 1, 2^64 - 1] = some [5035, 950]
-- a = b = 2^70 = [0, 2^6, 0, 0]; c = 2^140 + 1 = [1, 0, 2^12, 0].
-- a·b = 2^140 < c, so the result is a·b itself, encoded as [0, 0, 2^12, 0].
#guard fpMul (p := Primes.bn254) 64 4 [0, 2^6, 0, 0] [0, 2^6, 0, 0] [1, 0, 2^12, 0] = some [0, 0, 2^12, 0]
-- length mismatch
#guard fpMul (p := 17) 4 2 [3] [5, 0] [7, 0] = none
-- limb 16 ≥ 2^4 is out of range
#guard fpMul (p := 17) 4 2 [16, 0] [5, 0] [7, 0] = none
-- C = 0
#guard fpMul (p := 17) 4 2 [3, 0] [5, 0] [0, 0] = none

end TestFpMul
