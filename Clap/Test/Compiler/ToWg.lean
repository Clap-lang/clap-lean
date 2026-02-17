import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Spec Compiler Lang

variable {p : Nat} [Fact (Nat.Prime p)]

structure Point (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def ToWg.ex₁_aux {p : Nat} [Fact (Nat.Prime p)] [Core p] (var : Type) : Circuit p var := .nil
def ToWg.ex₁ {p : Nat} [Fact (Nat.Prime p)] [Core p] (_point : Point p) : Option Unit := accept

/--
info: def - fun {p : ℕ} [Fact (Nat.Prime p)] [Core p] (_point : Point p) =>
  (toWg' ToWg.ex₁_aux).run { toList := [_point.x, _point.y, _point.z] }
---
info: type - {p : ℕ} → [Fact (Nat.Prime p)] → [Core p] → Point p → Array (ZMod p)
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  let decl ← find! `ToWg.ex₁
  let declC ← find! `ToWg.ex₁_aux
  lambdaTelescope decl.value! fun args _ ↦ do
    let toWgd ← wg declC.name args
    logInfo m!"def - {toWgd}"
    logInfo m!"type - {←inferType toWgd}"

end Compiler

end Test

end Clap
