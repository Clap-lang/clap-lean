import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap.Compiler Meta Lang

structure Point2 (p : Nat) where
  x : ZMod p
  y : ZMod p

structure Point3 (p : Nat) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def Serialise.ex₁ {p} [Core p] (p₁ : Point2 p) (p₂ : Point3 p) : Option Unit := do
  Spec.Compiler.eq0 (p₁.x + p₂.z)
  Spec.Compiler.accept

/--
info: def - fun {p : ℕ} (p₁_circuit : Vector (ZMod Primes.babybear) 2) (p₂_circuit : Vector (ZMod Primes.babybear) 3) => do
  Spec.Compiler.eq0 (p₁_circuit[0] + p₂_circuit[2])
  some Spec.Compiler.accept
---
info: type - {p : ℕ} → Vector (ZMod Primes.babybear) 2 → Vector (ZMod Primes.babybear) 3 → Option Unit
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  let serialised ← serialise `Primes.babybear (←find! `Serialise.ex₁).value!
  logInfo m!"def - {serialised}"
  logInfo m!"type - {←inferType serialised}"

end Compiler

end Test

end Clap
