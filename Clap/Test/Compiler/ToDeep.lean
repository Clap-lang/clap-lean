import Clap.Spec
import Clap.Compiler.Deep
import Clap.Test.Wheels
import Clap.SpecUint
import Clap.Compiler.Basic

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Lang

open Spec Compiler in
def ToDeep.ex₁ {p:ℕ} [Fact (Nat.Prime p)] [Core p] (x:ZMod p) : Option Unit :=
  let y : ZMod p := 1
  let z : ZMod p := is_zero y
  do
  let _j <- num2bits 2 y
  eq0 (x+(1:ZMod p) * x-y+z) -- cannot use j[0]!
  accept

/--
info: def - fun (p : ℕ) [Fact (Nat.Prime p)] [Core p] (var : Type) =>
  Circuit.lam fun (x : var) =>
    Circuit.share (Exp.c 1) fun (y : var) =>
      Circuit.is_zero (Exp.v y) fun (z : var) =>
        Circuit.num2bits 2 (Exp.v y) fun (vars : List var) =>
          Circuit.eq0 ((((Exp.v x).add ((Exp.c 1).mul (Exp.v x))).sub (Exp.v y)).add (Exp.v z))
            ((fun (x : PUnit.{1}) => Circuit.nil) ())
---
info: type - (p : ℕ) → [Fact (Nat.Prime p)] → [Core p] → (var : Type) → Circuit p var
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep (←find! `ToDeep.ex₁).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"


/- TODO we need to support the following two cases that are currently failing. -/

open Spec Compiler in
def ToDeep.ex₂ {p:ℕ} [Fact (Nat.Prime p)] (x:ZMod p) : Option Unit := do
  let j <- num2bits 2 x
  eq0 (j[0]!)
  accept

/--
info: compileExp: no match
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep (←find! `ToDeep.ex₂).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"


open Spec Compiler in
def ToDeep.ex₃ {p:ℕ} [Fact (Nat.Prime p)] (x:ZMod p) : Option Unit := do
  eq0 (is_zero x + share x)
  accept

/--
info: compileExp: no match
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep (←find! `ToDeep.ex₃).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"

open Spec Compiler in
def ToDeep.ex₄ {p : ℕ} [Fact (Nat.Prime p)] [Core p] (x y : ZMod p) : Option Unit := do
  (do
     eq0 x
     eq0 y
     eq0 y)
  some accept

/--
info: def - fun (p : ℕ) [Fact (Nat.Prime p)] [Core p] (var : Type) =>
  Circuit.lam fun (x : var) =>
    Circuit.lam fun (y : var) =>
      Circuit.eq0 (Exp.v x)
        ((fun (x_1 : Unit) =>
            Circuit.eq0 (Exp.v y)
              ((fun (x_2 : Unit) => Circuit.eq0 (Exp.v y) ((fun (x : PUnit.{1}) => Circuit.nil) ())) ()))
          ())
---
info: type - (p : ℕ) → [Fact (Nat.Prime p)] → [Core p] → (var : Type) → Circuit p var
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep (←Compiler.linearise (←find! `ToDeep.ex₄).value!)
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"

end Compiler

end Test

end Clap
