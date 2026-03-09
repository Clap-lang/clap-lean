import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Spec Compiler Lang ZMod

def produceEq0 {p} (l : List (ZMod p)) (h : l ≠ []) : Option Unit :=
  match l with
  | [hd] => do
    Clap.Spec.Compiler.eq0 hd
  | x₁ :: x₂ :: tl => do
    Clap.Spec.Compiler.eq0 x₁
    produceEq0 (x₂ :: tl) (by simp)

def Reduce.ex₀ {p} [Core p] (x y : ZMod p) : Option Unit := do
  produceEq0 [x, x, y] (by simp)
  accept

/--
info: Compiled Reduce.ex₀ into Reduce.ex₀_ser.
---
info: Wg for Reduce.ex₀ is Reduce.ex₀_ser_wg.
-/
#guard_msgs(info, whitespace := lax) in
#compile Reduce.ex₀ using Primes.babybear

def Reduce.ex₁ (x y : ZMod Primes.babybear) : Option Unit := do
  eq0 x
  eq0 x
  eq0 y
  accept

/--
info: Compiled Reduce.ex₁ into Reduce.ex₁_ser.
---
info: Wg for Reduce.ex₁ is Reduce.ex₁_ser_wg.
-/
#guard_msgs(info, whitespace := lax) in
#compile Reduce.ex₁ using Primes.babybear

def Reduce.ex₂ (x y : ZMod Primes.babybear) : Option Unit := do
  let z := [x, x, y].map id
  produceEq0 z (by simp [z])
  accept

/--
info: Compiled Reduce.ex₂ into Reduce.ex₂_ser.
---
info: Wg for Reduce.ex₂ is Reduce.ex₂_ser_wg.
-/
#guard_msgs(info, whitespace := lax) in
#compile Reduce.ex₂ using Primes.babybear

example : Reduce.ex₀_ser = Reduce.ex₁_ser := rfl

example : Reduce.ex₀_ser = Reduce.ex₂_ser := rfl

end Compiler

end Test

end Clap
