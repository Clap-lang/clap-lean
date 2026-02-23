import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Spec Compiler Lang ZMod

structure Compile.Point (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

structure Compile.Point' (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p
  w : ZMod p

def Compile.ex₀ {p : ℕ} [Core p] (point₁ point₂ : Point p) (point₃ : Point' p) : Option Unit := do
  eq0 (point₁.x + point₃.w)
  eq0 (point₂.x + point₁.z)
  accept

/--
info: Compiled Compile.ex₀ into Compile.ex₀_ser.
---
info: Wg for Compile.ex₀ is Compile.ex₀_ser_wg.
-/
#guard_msgs(info, whitespace := lax) in
#compile Compile.ex₀ using Primes.babybear

/--
info: def Compile.ex₀_ser : (var : Type) → Circuit Primes.babybear var :=
fun (var : Type) =>
  Circuit.lam fun (curried0_point₁_ser : var) =>
    Circuit.lam fun (curried1_point₁_ser : var) =>
      Circuit.lam fun (curried2_point₁_ser : var) =>
        Circuit.lam fun (curried0_point₂_ser : var) =>
          Circuit.lam fun (curried1_point₂_ser : var) =>
            Circuit.lam fun (curried2_point₂_ser : var) =>
              Circuit.lam fun (curried0_point₃_ser : var) =>
                Circuit.lam fun (curried1_point₃_ser : var) =>
                  Circuit.lam fun (curried2_point₃_ser : var) =>
                    Circuit.lam fun (curried3_point₃_ser : var) =>
                      Circuit.eq0 ((Exp.v curried0_point₁_ser).add (Exp.v curried3_point₃_ser))
                        ((fun (x : PUnit.{1}) =>
                            Circuit.eq0 ((Exp.v curried0_point₂_ser).add (Exp.v curried2_point₁_ser))
                              ((fun (x : PUnit.{1}) => Circuit.nil) ()))
                          ())
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₀_ser

/--
info: def Compile.ex₀_ser_wg : Wg Primes.babybear →
  Compile.Point Primes.babybear →
    Compile.Point Primes.babybear → Compile.Point' Primes.babybear → Array (ZMod Primes.babybear) :=
fun (wg : Wg Primes.babybear) (point₁ point₂ : Compile.Point Primes.babybear)
    (point₃ : Compile.Point' Primes.babybear) =>
  wg.run
    { toList := [point₁.x, point₁.y, point₁.z, point₂.x, point₂.y, point₂.z, point₃.x, point₃.y, point₃.z, point₃.w] }
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₀_ser_wg

end Compiler

end Test

end Clap
