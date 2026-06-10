import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

def testInnerReturn : Option ℕ := do
  let x ← F 1
  let y ← F (←(fun (x: ℕ) => do
    return x) 3)
  let z ← F 3
  pure z

set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTest ``testInnerReturn


def exex' : Option ℕ := do
  let z ← F 2
  let x ← H 4
  let y ← (do let x ← G (x + z); let y ← G x; H (x + z))
  H y
#eval exex' == F 8

def exex'' : Option ℕ := do
  let z ← F 2
  let x ← #v[1, 2].mapM (fun _ ↦ pure 4)
  let y ← (do let x ← G x[1]; let y ← G x; H (x + z))
  H y

#check @Option.bind_assoc

set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTest ``exex''


opaque A : Nat → Option Nat
opaque B : Nat → Option Nat
opaque C : Nat → Option Nat
opaque D : Nat → Option Nat
opaque E : Nat → Option Nat

def eboom (vec : Vector Nat 4) : Option Unit := do
  let x ←
    (do
      let _ ← A 0
      let x ←
        (do let y ← do
            let _ ← B 1
            let res ←
              (do let w ← C 2
                  D 5)
            E res)
      F x
    )
  discard (G x)

-- set_option trace.Clap.Compile true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile.dbg true in
-- #eval runTest ``eboom

end NewTraversal

namespace ExampruSym
