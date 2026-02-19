import Clap.Compiler.Basic
import Clap.Compilation
import Clap.R1CS
import Clap.Lang

namespace Circuit

open Clap Lang

open Core

structure Point2 (p : ℕ) where
  x : ZMod p
  y : ZMod p

structure Point3 (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def test {p:ℕ} [Core p] (x y z : Core.F p) (p₁ : Point2 p) (p₂ : Point3 p) : Option Unit := do
  eq0 (x * (y - z) + z)
  accept p

open ZMod

abbrev test' (x y z : ZMod Primes.babybear)
             (p₁ : Point2 Primes.babybear) (p₂ : Point3 Primes.babybear) : Option Unit := do
  Spec.Compiler.eq0 (x * (y - z) + p₁.x + p₂.x)
  Spec.Compiler.accept

/--
info: Compiled Circuit.test' into Circuit.test'_ser.
---
info: Wg for Circuit.test' is Circuit.test'_ser_wg.
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#compile Circuit.test' using Primes.babybear

/--
info: def Circuit.test'_ser_wg : Wg Primes.babybear →
  ZMod Primes.babybear →
    ZMod Primes.babybear →
      ZMod Primes.babybear → Point2 Primes.babybear → Point3 Primes.babybear → Array (ZMod Primes.babybear) :=
fun (wg : Wg Primes.babybear) (x y z : ZMod Primes.babybear) (p₁ : Point2 Primes.babybear)
    (p₂ : Point3 Primes.babybear) =>
  wg.run { toList := [x, y, z, p₁.x, p₁.y, p₂.x, p₂.y, p₂.z] }
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Circuit.test'_ser_wg

/--
info: def Circuit.test'_ser : (var : Type) → Circuit Primes.babybear var :=
fun (var : Type) =>
  Circuit.lam fun (x : var) =>
    Circuit.lam fun (y : var) =>
      Circuit.lam fun (z : var) =>
        Circuit.lam fun (curried0_p₁_ser : var) =>
          Circuit.lam fun (curried1_p₁_ser : var) =>
            Circuit.lam fun (curried0_p₂_ser : var) =>
              Circuit.lam fun (curried1_p₂_ser : var) =>
                Circuit.lam fun (curried2_p₂_ser : var) =>
                  Circuit.eq0
                    ((((Exp.v x).mul ((Exp.v y).sub (Exp.v z))).add (Exp.v curried0_p₁_ser)).add
                      (Exp.v curried0_p₂_ser))
                    ((fun (x : PUnit.{1}) => Circuit.nil) ())
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Circuit.test'_ser

def wg := toWg' Circuit.test'_ser
/--
info: def Circuit.wg : Wg Primes.babybear :=
toWg' test'_ser
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print wg

def wg' := Circuit.test'_ser_wg wg
/--
info: def Circuit.wg' : ZMod Primes.babybear →
  ZMod Primes.babybear →
    ZMod Primes.babybear → Point2 Primes.babybear → Point3 Primes.babybear → Array (ZMod Primes.babybear) :=
test'_ser_wg wg
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print wg'

def cs := Clap.toCs' (Circuit.test'_ser)
def r1cs := Clap.toR1CS (Circuit.test'_ser)

/-- info: Circuit.cs : Cs' Primes.babybear -/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#check cs

/-- info: eq0 (((v1 * (v2 - v3)) + v4) + v6) nil -/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#eval r1cs

end Circuit
