import Clap.Spec
import Clap.Compiler.Deep
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta

open Spec Compiler in
def ToDeep.ex₁ (x : ZMod Primes.babybear) : Option Unit :=
  let y : ZMod Primes.babybear := share 1
  let z : ZMod Primes.babybear := is_zero y
  do
  let _j := num2bits 2 y
  eq0 (x+(1:ZMod Primes.babybear) * x-y+z) -- cannot use j[0]!
  accept

/--
info: def - fun (var : Type) =>
  Circuit.lam fun (x : var) =>
    Circuit.share (Exp.c 1) fun (y : var) =>
      Circuit.is_zero (Exp.v y) fun (z : var) =>
        Circuit.num2bits 2 (Exp.v y) fun (vars : List var) =>
          Circuit.eq0 ((((Exp.v x).add ((Exp.c 1).mul (Exp.v x))).sub (Exp.v y)).add (Exp.v z))
            ((fun (x : PUnit.{1}) => Circuit.nil) ())
---
info: type - (var : Type) → Circuit Primes.babybear var
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep `Primes.babybear (←find! `ToDeep.ex₁).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"


/- TODO we need to support the following two cases that are currently failing. -/

open Spec Compiler in
def ToDeep.ex₂ (x : ZMod Primes.babybear) : Option Unit := do
  let j := num2bits 2 x
  eq0 (j[0]!)
  accept

/-- info: compileExp: no match for vars[0]! -/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep `Primes.babybear (←find! `ToDeep.ex₂).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"


open Spec Compiler in
def ToDeep.ex₃ (x : ZMod Primes.babybear) : Option Unit := do
  eq0 (is_zero x + share x)
  accept

/-- info: compileExp: no match for Spec.Compiler.is_zero x -/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← toDeep `Primes.babybear (←find! `ToDeep.ex₃).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"

end Compiler

end Test

end Clap
