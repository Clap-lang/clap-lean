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
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testInnerReturn

def testRightBind : Option ℕ := do
  let x ← F 1
  let y ← F (x + 10)
  return y
set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testRightBind

def testLeftBind : Option ℕ := do
  let y ← F ((←do
    let x ← F 1;
    return x) + 10
  )
  return y

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testLeftBind

def testTreeBindNested : Option ℕ := do
  let a ← F 1
  let B ← F 2
  let b ← (
    do let x ← F (a + B)
       let y ← F (x + 10)
       let z ← F (x + 42)
       return y + y + B + z
  )
  let w ← F (b + 100)
  let y ← F (b + 200)
  let c ← (
    do let x ← F 1000;
       let y ← F (x + 10000)
       let z ← (do
         let a ← F 3
         let b ← F (a + w)
         let c ← F (a + b)
         let d ← F 4
         return c + d)
       return y + a + w + z + B + w
  )
  let z ← F (c + 100000)
  return y + z + a + b

def flattenedTreeBindNested : Option ℕ := do
  let a ← F 1
  let B ← F 2
  let x ← F (a + B)
  let y ← F (x + 10)
  let z ← F (x + 42)
  let b ← pure (y + y + B + z)
  let w ← F (b + 100)
  let y ← F (b + 200)
  let x ← F 1000;
  let y' ← F (x + 10000)
  let a' ← F 3
  let b' ← F (a' + w)
  let c' ← F (a' + b')
  let d' ← F 4
  let y'' ← pure (c' + d')
  let c ← pure (y' + a + w + y'' + B + w)
  let z ← F (c + 100000)
  return y + z + a + b

def testTreeBind : Option ℕ := do
  let b ← (
    do let x ← F 1
       let y ← F (x + 10)
       return y
  )
  let y ← F (b + 100)
  let c ← (
    do let x ← F 1000;
       let y ← F (x + 10000)
       return y
  )
  let z ← F (c + 100000)
  return y + z -- `#2 + #0`

def flattenedTreeBind : Option ℕ := do
  let x ← F 1
  let y ← F (x + 10)
  let y ← pure y
  let y ← F (y + 100)
  let x ← F 1000
  let y' ← F (x + 10000)
  let y' ← pure y'
  let z ← F (y' + 100000)
  pure (y + z) -- `#4 + #0`

example :
  testTreeBind =
  (((F 1).bind fun x => (F (x.add 10)).bind fun y => some y).bind fun __do_lift =>
    (F (__do_lift.add 100)).bind fun y =>
      ((F 1000).bind fun x => (F (x.add 10000)).bind fun y => some y).bind fun __do_lift =>
        (F (__do_lift.add 100000)).bind fun z => some (y.add z))
:=
  rfl

example :
  testTreeBind = flattenedTreeBind
:= by
  simp only [
    testTreeBind,
    flattenedTreeBind
  ]
  simp only [
    bind_assoc
  ]

#print testTreeBind

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testTreeBind

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testTreeBindNested

def exex' : Option ℕ := do
  let z ← F 2
  let x ← H 4
  let y ← (do let x ← G (x + z); let y ← G x; H (x + z))
  H y

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``exex'

def exex'' : Option ℕ := do
  let z ← F 2
  let x ← #v[1, 2, 3, 4].mapM (fun _ ↦ pure 4)
  let y ← (do let x ← G x[0]; let y ← G x; H (x + z))
  H y

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``exex''

opaque A : Nat → Option Nat
opaque B : Nat → Option Nat
opaque C : Nat → Option Nat
opaque D : Nat → Option Nat
opaque E : Nat → Option Nat

abbrev eboom (vec : Vector Nat 4) : Option Unit := do
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

def eboomWithArgs := eboom #v[1,2,3,4]

#eval runOptionNTestByName ``eboomWithArgs

def bvars : Option ℕ := do
  let b ← (do
    let z : ℕ ← #v[1, 2].foldlM (fun acc _ ↦ return acc) 42
    return z
  )
  b

set_option pp.notation false in
set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName `ExampruSym.NewTraversal.bvars


end NewTraversal

namespace ExampruSym
