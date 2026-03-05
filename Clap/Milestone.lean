import Clap.Lang
import Clap.Compiler.Basic
import Clap.Cfold
import Clap.Compilation
import Clap.Quadratic
--import Clap.Sha2.Circuit
import Clap.BackEndFirstOrder


-- open Clap

-- variable {p : ℕ} [Fact (Nat.Prime p)]

-- -- TODO we could make eq0 cps

-- def Cid {var} : Circuit p var → Circuit p var
--   | .nil => .nil
--   | .eq0 e c => .eq0 e (Cid c)
--   | .lam k => .lam fun x ↦ Cid (k x)
--   | .is_zero e k => .is_zero e fun x ↦ Cid (k x)
--   | .share e k => .share e fun x ↦ Cid (k x)
--   | .num2bits w e k => .num2bits w e fun x ↦ Cid (k x)

-- def Cid' (c:Circuit' p) : Circuit' p := fun var => Cid (c var)

-- -- #eval! ((Cid' test_circ) ℕ)


-- def mkEq0 (p n:ℕ): Circuit' p := fun _var =>
--   List.foldr (fun _ acc => .eq0 (.c 0) acc) .nil [0:n].toList

-- --#eval ((Cid' (mkEq0 Primes.babybear 3000)) ℕ)

-- def mkLam (p n:ℕ): Circuit' p := fun _var =>
--   List.foldr (fun _ acc => .lam fun _ => acc) .nil [0:n].toList

-- def mkLamExp (p n:ℕ): Circuit' p := fun var =>
--   let rest : Circuit p var := .eq0 (.c 1 + .c 2) .nil
--   List.foldr (fun _ acc => .lam fun _ => acc) rest [0:n].toList

-- --#eval ((Cid' (mkLam Primes.babybear 5000)) ℕ)

open Primes
open Clap
open Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 32)]

variable [Core p]

open Core
open ZMod

-- set_option pp.all true

def test {p:ℕ} [inst : Core p] (_x : F p) : Option Unit := do
  eq0 ((0:F p))
  accept p

example {x : F Primes.goldilocks} : test x = sorry := by
  unfold test
  unfold OfNat.ofNat
  unfold Zero.toOfNat0
  dsimp -zeta only
  unfold Zero.zero
  unfold_projs
  dsimp
  unfold OfNat.ofNat
  unfold instOfNatNat
  dsimp
  unfold OfNat.ofNat
  unfold instOfNatNat
  dsimp
  unfold OfNat.ofNat
  unfold instOfNatNat
  dsimp
  unfold OfNat.ofNat
  unfold instOfNatNat
  dsimp
  unfold OfNat.ofNat
  unfold instOfNatNat
  dsimp
  dsimp only


--#print test

def minimal : (var : Type) → Circuit p var :=
fun _var => Circuit.eq0 ((Exp.c 0).sub (Exp.c 0)) ((fun _x => Circuit.nil) ())

def minimal' : (var : Type) → Circuit p var := fun _var => Circuit.nil

open Clap.Lang.ZMod

-- #compile minimal using Primes.goldilocks

--#reduce ((1:ZMod 2) - 1)

#compile test using Primes.goldilocks

-- set_option pp.deepTerms true
-- set_option format.indent 0

--#print test_ser

--#eval! (test_ser ℕ)

def main (args : List String) : IO UInt32 := do
  IO.println s!"snarkjs ri {args[0]!}"
  -- let c := (Cid' (mkEq0 Primes.babybear 100))

  -- 100000 works, 1000000 overflows
  -- let cs := (Clap.toCs' (mkLam Primes.babybear 100000))
  -- let cs := (Clap.toCs' (mkLamExp Primes.babybear 1000))

  let cs : Cs' goldilocks := Clap.toCs' test_ser
  -- let cs : Cs' goldilocks := Clap.toCs' minimal

  if s!"{cs ℕ}" = "" then return 1 else
  return 0
