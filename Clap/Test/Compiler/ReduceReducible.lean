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
info: Compiled Clap.Test.Compiler.Reduce.ex₀ into Clap.Test.Compiler.Reduce.ex₀_circuit.
---
info: Wg for Clap.Test.Compiler.Reduce.ex₀ is Clap.Test.Compiler.Reduce.ex₀_wg_wrap.
-/
#guard_msgs(info, whitespace := lax) in
#compile Reduce.ex₀ using Primes.babybear

def Reduce.ex₁ {p} [Core p] (x y : ZMod p) : Option Unit := do
  eq0 x
  eq0 x
  eq0 y
  accept

/--
info: Compiled Clap.Test.Compiler.Reduce.ex₁ into Clap.Test.Compiler.Reduce.ex₁_circuit.
---
info: Wg for Clap.Test.Compiler.Reduce.ex₁ is Clap.Test.Compiler.Reduce.ex₁_wg_wrap.
-/
#guard_msgs(info, whitespace := lax) in
#compile Reduce.ex₁ using Primes.babybear

def Reduce.ex₂ {p} [Core p] (x y : ZMod p) : Option Unit := do
  let z := [x, x, y].map id
  produceEq0 z (by simp [z])
  accept

/--
info: Compiled Clap.Test.Compiler.Reduce.ex₂ into Clap.Test.Compiler.Reduce.ex₂_circuit.
---
info: Wg for Clap.Test.Compiler.Reduce.ex₂ is Clap.Test.Compiler.Reduce.ex₂_wg_wrap.
-/
#guard_msgs(info, whitespace := lax) in
#compile Reduce.ex₂ using Primes.babybear

example : Reduce.ex₀_circuit = Reduce.ex₁_circuit := rfl

example : Reduce.ex₀_circuit = Reduce.ex₂_circuit := rfl

end Compiler

end Test

end Clap
