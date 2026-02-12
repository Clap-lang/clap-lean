import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap.Compiler Meta

structure Point2 (p : Nat) where
  x : ZMod p
  y : ZMod p

structure Point3 (p : Nat) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def ex₀ {p : Nat} (p₁ : Point2 p) (p₂ : Point3 p) : Option Unit := do
  Spec.Compiler.eq0 (p₁.x + p₂.z)
  Spec.Compiler.accept

/--
info: def -
  fun {p : ℕ} (p₁_ser : Vector (ZMod p) 2) (p₂_ser : Vector (ZMod p) 3) => do
    Spec.Compiler.eq0 (p₁_ser[0] + p₂_ser[2])
    some Spec.Compiler.accept
---
info: type -
  {p : ℕ} → Vector (ZMod p) 2 → Vector (ZMod p) 3 → Option Unit
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  let serialised ← serialise `p (←find! `ex₀).value!
  logInfo m!"def - {serialised}"
  logInfo m!"type - {←inferType serialised}"

end Compiler

end Test

end Clap
