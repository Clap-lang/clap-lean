import Clap.Primes
import Clap.Spec

namespace Clap.Lang

class Core (p : ℕ) : Type _ where
  F           : Type
  [instF      : Field F]
  [instFChar  : CharP F p]
  FB          : Type
  [instFB     : Field FB]
  [instFBChar : CharP FB p]
  convert     : FB → F -- true = 1, false = 0
  const       : ZMod p → F
  accept      : Unit
  eq0         : F → Option Unit
  share       : F → F
  shareB      : FB → FB
  isZero      : F → FB
  num2bits    : ℕ → F → Option (List FB)
  bits2num    : List FB → F

  [onlyForDebugF  : ToString F  ]
  [onlyForDebugFB : ToString FB ]

attribute [instance] Core.instF Core.instFChar Core.instFB Core.instFBChar Core.onlyForDebugF Core.onlyForDebugFB

namespace ZMod

open Clap.Spec

/-
  This instance should be avaible only when proving or testing a
  circuit, never while writing it. The risk is that a circuit which
  breaks the abstraction of Core won't be compilable.
-/
scoped instance instCoreZMod (p:ℕ) [Fact (Nat.Prime p)] : Core p where
  F := ZMod p
  FB := ZMod p
  convert := id
  const := id
  accept := Compiler.accept
  eq0 := Compiler.eq0
  share := Compiler.share
  shareB := Compiler.share
  isZero := Compiler.is_zero
  num2bits := Compiler.num2bits
  bits2num := Compiler.bits2num

/-
TODO it should be possible to replace the extended definition below with this definition but there is an error
class Extended (p:ℕ) [Fact (Nat.Prime p)] : Type _ extends Core p, DecidableEq (Core.F p)
-/

class extended (p:ℕ) [Fact (Nat.Prime p)] [Core p] : Type _ where
  ins : Core p
  [i₀ : DecidableEq (Core.F p)]
  [i₁ : {n:ℕ} → OfNat (Core.F p) n]

attribute [instance] extended.i₀ extended.i₁

scoped instance bla (p:ℕ) [Fact (Nat.Prime p)] : extended p where
  ins := instCoreZMod p
  i₀ := inferInstanceAs (DecidableEq (ZMod p))
  i₁ := inferInstanceAs ({n:ℕ} → OfNat (ZMod p) n)

end ZMod

end Clap.Lang
