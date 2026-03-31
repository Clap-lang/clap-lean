import Clap.Spec
import Clap.Compiler.AddLets
import Clap.Test.Wheels

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta

open Spec Compiler in
def duplicate (x : ZMod Primes.babybear) : Option Unit := do
  eq0 (x + share 1)
  eq0 (x + share 1)
  eq0 (x + isZero 1)
  eq0 (x + isZero 1)
  accept

/--
info: def - fun (x : ZMod Primes.babybear) =>
  let x_1 := Spec.Compiler.share 1;
  do
  Spec.Compiler.eq0 (x + x_1)
  Spec.Compiler.eq0 (x + x_1)
  let x_4 : ZMod Primes.babybear := Spec.Compiler.isZero 1
  Spec.Compiler.eq0 (x + x_4)
  Spec.Compiler.eq0 (x + x_4)
  some Spec.Compiler.accept
---
info: type - ZMod Primes.babybear → Option Unit
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← addLets (←find! `duplicate).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"

open Spec Compiler in
def nested (x : ZMod Primes.babybear) : Option Unit := do
  eq0 (x + share (share 1 + isZero 2))
  accept

/--
info: def - fun (x : ZMod Primes.babybear) =>
  let x_1 := Spec.Compiler.share 1;
  let x_2 := Spec.Compiler.isZero 2;
  let x_3 := Spec.Compiler.share (x_1 + x_2);
  do
  Spec.Compiler.eq0 (x + x_3)
  some Spec.Compiler.accept
---
info: type - ZMod Primes.babybear → Option Unit
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
run_elab do
  try
    let deep ← addLets (←find! `nested).value!
    logInfo m!"def - {deep}"
    logInfo m!"type - {←inferType deep}"
  catch e =>
    logInfo m!"{(e.toMessageData)}"

end Compiler

end Test

end Clap
