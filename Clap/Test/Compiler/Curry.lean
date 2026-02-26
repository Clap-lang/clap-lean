import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap.Compiler Meta

def Curry.ex₁ (p₁ : Vector (ZMod Primes.babybear) 2) (p₂ : Vector (ZMod Primes.babybear) 3) : Option Unit := do
  Spec.Compiler.eq0 (p₁[0] + p₂[2])
  Spec.Compiler.accept

/--
info: def - fun (curried0_p₁ curried1_p₁ curried0_p₂ curried1_p₂ curried2_p₂ : ZMod Primes.babybear) => do
  Spec.Compiler.eq0 (curried0_p₁ + curried2_p₂)
  some Spec.Compiler.accept
---
info: type - ZMod Primes.babybear →
  ZMod Primes.babybear → ZMod Primes.babybear → ZMod Primes.babybear → ZMod Primes.babybear → Option Unit
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  let curried ← Clap.Compiler.curry `Primes.babybear (←find! `Curry.ex₁).value!
  logInfo m!"def - {curried}"
  logInfo m!"type - {←inferType curried}"

end Compiler

end Test

end Clap
