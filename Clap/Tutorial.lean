import Clap.SpecUint

open Clap.Lang

namespace FirstSteps

namespace SafeSpace
/-
  First we assume a prime, and Core instance that over that prime.
  Optionally we can require the prime to be large enough to fit the
  numerical types we are planning to use. In this example require at
  least 32 bits.
-/
variable {p : ℕ} [Fact (Nat.Prime p)] [Core p] [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)]

open Core

/-
  We must have an instance of Core over our abstract prime in order to
  write our circuits.
-/
#synth Core p

def checkAdd (a b o : F p) : Option Unit := do
  Core.eq0 (a + b - o)
  Core.accept (p:=p)

end SafeSpace

namespace TestAndProve

abbrev p := Primes.goldilocks
abbrev F := ZMod p

open Clap.Lang -- here we have an instance of the Core class
open Core

#guard SafeSpace.checkAdd (p:=p) 5 6 11 = some ()
#guard SafeSpace.checkAdd (p:=p) 1 1 5 = none

theorem checkAddCorrect (a b : F) :
  SafeSpace.checkAdd (p:=p) a b (a+b) = some () := by
  unfold SafeSpace.checkAdd accept
  rw [Test.equiv_eq0]
  rw [Clap.Spec.Compiler.SeeThrough.equiv_eq0]
  simp

end TestAndProve

end FirstSteps


namespace LivingDangerously

namespace StillSafeSpace
/-
  If the circuit we are writing is for a fixed field, for example
  Poseidon or Jubjub. We can make the prime concrete so long as the
  Core instance remains abstract.
-/
abbrev p := Primes.bn254

variable [Core p] -- not a concrete instance

open Core

/--
error: failed to synthesize instance of type class
  Core p

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in
#guard (Core.F p = ZMod p)

/-
  In this case the argument `b` is compile time parameter that cannot
  be confused with `a` or `o`. The only way to introduce `b` into the
  circuit is through the `const` operator.
-/
def checkAddConst (b : ZMod p) (a o : F p) : Option Unit := do
  Core.eq0 (a + (Core.const b) - o)
  Core.accept (p:=p)

end StillSafeSpace

end LivingDangerously
