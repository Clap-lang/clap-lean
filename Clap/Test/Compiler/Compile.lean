import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Spec Compiler Lang

structure Compile.Point (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

structure Compile.Point' (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p
  w : ZMod p

def Compile.ex₀ {p : ℕ} (point₁ point₂ : Point p) (point₃ : Point' p) : Option Unit := do
  eq0 (point₁.x + point₃.w)
  eq0 (point₂.x + point₁.z)
  accept

/--
info: Compiled Compile.ex₀ into Compile.ex₀_circuit.
---
info: Wg for Compile.ex₀ is Compile.ex₀_wg_wrap.
-/
#guard_msgs(info, whitespace := lax) in
#compile Compile.ex₀ using Primes.babybear

/--
info: def Compile.ex₀_circuit : (var : Type) → Circuit Primes.babybear var :=
fun (var : Type) =>
  Circuit.lam fun (curried0_point₁_circuit : var) =>
    Circuit.lam fun (curried1_point₁_circuit : var) =>
      Circuit.lam fun (curried2_point₁_circuit : var) =>
        Circuit.lam fun (curried0_point₂_circuit : var) =>
          Circuit.lam fun (curried1_point₂_circuit : var) =>
            Circuit.lam fun (curried2_point₂_circuit : var) =>
              Circuit.lam fun (curried0_point₃_circuit : var) =>
                Circuit.lam fun (curried1_point₃_circuit : var) =>
                  Circuit.lam fun (curried2_point₃_circuit : var) =>
                    Circuit.lam fun (curried3_point₃_circuit : var) =>
                      Circuit.eq0 ((Exp.v curried0_point₁_circuit).add (Exp.v curried3_point₃_circuit))
                        ((fun (__r : Unit) =>
                            Circuit.eq0 ((Exp.v curried0_point₂_circuit).add (Exp.v curried2_point₁_circuit))
                              ((fun (__r : Unit) => Circuit.nil) ()))
                          ())
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₀_circuit

/--
info: def Compile.ex₀_wg_wrap : Wg Primes.babybear →
  Compile.Point Primes.babybear →
    Compile.Point Primes.babybear → Compile.Point' Primes.babybear → Array (ZMod Primes.babybear) :=
fun (wg : Wg Primes.babybear) (point₁ point₂ : Compile.Point Primes.babybear)
    (point₃ : Compile.Point' Primes.babybear) =>
  wg.run
    { toList := [point₁.x, point₁.y, point₁.z, point₂.x, point₂.y, point₂.z, point₃.x, point₃.y, point₃.z, point₃.w] }
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₀_wg_wrap


-- TODO should work with Core
-- def Compile.ex₁ {p : ℕ} [Core p] (x : Core.F p) : Option Unit := do
--   let x := Core.share x
--   let y := Core.const (1:ZMod p)
--   let z := Core.isZero y
--   let k <- Core.num2bits 2 (x + Core.convert z)
--   -- TODO expand k
--   Core.eq0 (Core.convert k[0]!)
--   Core.accept p

open Spec.Compiler

def Compile.ex₁ {p : ℕ} (x : ZMod p) : Option Unit := do
  let x ← share x
  let y := (1:ZMod p)
  let z ← isZero y
  let _ ← num2bits 2 (x + z)
--  eq0 k[0]!
  accept

-- /--
-- info: Compiled Compile.ex₁ into Compile.ex₁_circuit.
-- ---
-- info: Wg for Compile.ex₁ is Compile.ex₁_wg_wrap.
-- -/
-- #guard_msgs(info, whitespace := lax) in
-- #compile Compile.ex₁ using Primes.babybear

-- /--
-- info: def Compile.ex₁_circuit : (var : Type) → Circuit Primes.babybear var :=
-- fun (var : Type) =>
--   Circuit.lam fun (x : var) =>
--     Circuit.share (Exp.v x) fun (x : var) =>
--       Circuit.isZero (Exp.c 1) fun (z : var) =>
--         Circuit.num2bits 2 ((Exp.v x).add (Exp.v z)) fun (vars : List var) => Circuit.nil
-- -/
-- #guard_msgs(info, whitespace := lax) in
-- set_option pp.funBinderTypes true in
-- #print Compile.ex₁_circuit


def Compile.adder {p : ℕ} [Fact (Nat.Prime p)] (x y : F p) : Option (F p) := do
  eq0 x
  eq0 y
  let z := x + y
  eq0 z
  return z

def Compile.test {p : ℕ} [Fact (Nat.Prime p)] (x y z : F p) : Option Unit := do
  let a ← adder x y
  let b ← adder y z
  eq0 (a - b)
  accept

/--
info: Compiled Compile.test into Compile.test_circuit.
---
info: Wg for Compile.test is Compile.test_wg_wrap.
-/
#guard_msgs in
#compile Compile.test using Primes.babybear

end Compiler

end Test

end Clap
