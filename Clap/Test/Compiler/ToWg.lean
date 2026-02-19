import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Spec Compiler

structure Point (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def ToWg.ex₁_aux (var : Type) : Circuit Primes.babybear var := .nil
def ToWg.ex₁ (_point : Point Primes.babybear) : Option Unit := accept

/--
info: def - fun (wg : Wg Primes.babybear) (_point : Point Primes.babybear) =>
  wg.run { toList := [_point.x, _point.y, _point.z] }
---
info: type - Wg Primes.babybear → Point Primes.babybear → Array (ZMod Primes.babybear)
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  let decl ← find! `ToWg.ex₁
  lambdaTelescope decl.value! fun args _ ↦ do
    let toWgd ← wg `Primes.babybear args
    logInfo m!"def - {toWgd}"
    logInfo m!"type - {←inferType toWgd}"

end Compiler

end Test

end Clap
