import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap.Compiler Meta Lang

def Curry.ex₁ {p : Nat} [Fact (Nat.Prime p)] [Core p] (p₁ : Vector (ZMod p) 2) (p₂ : Vector (ZMod p) 3) : Option Unit := do
  Spec.Compiler.eq0 (p₁[0] + p₂[2])
  Spec.Compiler.accept

/--
info: def - fun {p : ℕ} [Fact (Nat.Prime p)] [Core p]
    (curried0_p₁ curried1_p₁ curried0_p₂ curried1_p₂ curried2_p₂ : ZMod p) =>
  do
  Spec.Compiler.eq0 (curried0_p₁ + curried2_p₂)
  some Spec.Compiler.accept
---
info: type - {p : ℕ} → [Fact (Nat.Prime p)] → [Core p] → ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → Option Unit
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  let curried ← Clap.Compiler.curry `p (←find! `Curry.ex₁).value!
  logInfo m!"def - {curried}"
  logInfo m!"type - {←inferType curried}"

end Compiler

end Test

end Clap
