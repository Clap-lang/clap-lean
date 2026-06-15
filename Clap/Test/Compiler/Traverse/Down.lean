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

#eval Lean.ToExpr.toExpr testInnerReturn

-- Environment.find? ``testInnerReturn

set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTestByName ``testInnerReturn

def testRightBind : Option ℕ := do
  let x ← F 1
  let y ← F (x + 10)
  return y
set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTestByName ``testRightBind

def testLeftBind : Option ℕ := do
  let y ← F ((←do
    let x ← F 1;
    return x) + 10
  )
  return y
set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTestByName ``testLeftBind

-- def testTreeBind : Option ℕ := do
--   let y ← F ((←do
--     let x ← F 1;
--     let y ← F (x + 10)
--     return y) + 100
--   )
--   let z ← F ((←do
--     let x ← F 1000;
--     let y ← F (x + 10000)
--     return y) + 100000
--   )
--   return y + z

def testTreeBindNested : Option ℕ := do
  let a ← F 1
  let b ← F 2
  let b ← (
    do let x ← F (a + b)
       let y ← F (x + 10)
       let z ← F (x + 42)
       return y + y + b + z
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
       return y + a + w + z
  )
  let z ← F (c + 100000)
  return y + z + a + b

-- `e = λ x y z ↦ A`
-- `lambdaTlescope e fun args body ↦ ... mkLambdaFVars args body`
-- .lam x `t`

def flattenedTreeBindNested : Option ℕ := do
  let a ← F 1
  let b ← F 2
  let x ← F (a + b)
  let y ← F (x + 10)
  let z ← F (x + 42)
  let b ← pure (y + y + b + z)
  let w ← F (b + 100)
  let y ← F (b + 200)
  let x ← F 1000;
  let y' ← F (x + 10000)
  let a' ← F 3
  let b' ← F (a' + w)
  let c' ← F (a' + b')
  let d' ← F 4
  let y'' ← pure (c' + d')
  let c ← pure (y' + a + w + y'')
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

example : flattenedTreeBind = testTreeBind := by
  unfold flattenedTreeBind testTreeBind
  simp [bind_assoc, Option.bind_assoc]

open Lean Meta in
/--
TODO: Make tail rec.
-/
partial def planusEst (e : Expr) : Sym.Simp.SimpM (Array Expr) := do
  let res ← go e [0]
  logInfo m!"res: {res}"
  return res
  where
  go (e : Expr) (Γ : List ℕ) : Sym.Simp.SimpM (Array Expr) := do
    trace[Clap.Compile.dbg] m!"e[{Γ}]:\n{e}"
    match e.matchBindsE with
    | .some (action, func) =>
      match action.matchBindsE with
      | .some (b, g) =>
        let b ← go b Γ
        let g ← go g Γ
        let actions := b ++ g
        logInfo m!"↑[{actions.size.pred}]"
        -- `let x ← do a₁; a₂; a₃; ...; aₙ` offsets subsequent lambdas `n - 1` times
        let actions' ← go (func.liftLooseBVars 0 actions.size.pred) (actions.size :: Γ)
        return actions ++ actions'
      | _ =>
        let func ← go func Γ
        return #[action] ++ func
    | _ =>
      match e with
      | .lam (body := body) .. =>
        go body Γ
      | _ =>
        return #[e]

-- open Lean in
-- partial def planusEst' (e : Expr) (level : ℕ) (count : ℕ) (lams : ℕ) (lr : LR) : MetaM ℕ := do
--   let newLevel := newLevel (level := level)
--   -- logInfo m!"e[l={level}][c={count}][λ={lams}]:\n{e}"
--   if let .some (a, f) := e.matchBindsE
--   then
--     let level' := newLevel a
--     if level' != level then logInfo m!"push: {a}"
--     let left ← planusEst' a level' count lams Left
--     if level' != level then logInfo m!"pop"
--     let right ← planusEst' f level count lams Right
--     if level' != level then logInfo m!"left: {left} | right: {right}\ne: {e}\nrepl: {e.liftLooseBVars 0 left}"
--     return left + right
--   else
--     match e with
--     | .lam (body := body) .. =>
--       -- logInfo m!"lam[l={level}][c={count}][λ={lams}]: {e}"
--       planusEst' body level count lams.succ lr
--     | _ =>
--       logInfo m!"any[l={level}][c={count}][λ={lams}]:\n{e}\n==>\n{e.liftLooseBVars 1 count}"
--       return count.succ
    

  --   if let .some (b, g) := a.matchBindsE
  --   then
  --     let level := level.succ
  --     let count := 0
  --     let left ← planusEst a level count Left
  --     -- let count := left
  --     let right ← planusEst f level count Right
  --     logInfo m!"blocksize|L: {left} R: {right}"
  --     return left + right
  --   else
  --     let level := level
  --     let count := count
  --     let left ← planusEst a level count Left
  --     -- let count := left
  --     let right ← planusEst f level count Right
  --     logInfo m!"blocksize|L: {left} R: {right}"
  --     return right.succ
  -- else
  -- match e with
  -- | .lam (body := body) .. =>
  --   logInfo m!"lam[l={level}][c={count}]: {e}"
  --   planusEst body level count lr
  -- | _ => logInfo m!"any[l={level}][c={count}]: {e}"; return count.succ

set_option trace.Clap.Compile.dbg true in
open Lean in
run_meta do
  let rec go (e : Expr) : MetaM Unit :=
    match e with
    | .bvar .. => logInfo m!"{e}"
    | e => discard (e.traverseChildren (fun e ↦ go e >>= fun _ ↦ return e))
  
  -- let tree := (←getEnv).find? ``testTreeBind |>.get!.value!
  -- let flattree := (←getEnv).find? ``flattenedTreeBind |>.get!.value!
  let testTreeBindNested := (←getEnv).find? ``testTreeBindNested |>.get!.value!
  let flatNested := (←getEnv).find? ``flattenedTreeBindNested |>.get!.value!

  -- logInfo m!"{repr tree}"
  -- logInfo m!"{repr flattree}"

  -- let res ← (planusEst tree).run'.run
  -- logInfo m!"res: {res}"

  let res ← (planusEst testTreeBindNested).run'.run
  logInfo m!"resNested: {res}"
                        -- [1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 8, 3, 0, 4, 0, 10, 6]

  logInfo m!"not flat:"
  go testTreeBindNested -- [1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 6, 3, 0, 2, 0, 6, 4]
  logInfo m!"flat:"
  go flatNested
  -- [#1, #0, #0, #1 ,#1 ,#1 ,#3 ,#0 ,#0 ,#1 ,#0 ,#0 ,#4 ,#1 ,#0 ,#1 ,#0 ,#5 ,#14 ,#8 ,#0 ,#0 ,#9 ,#0 ,#16 ,#11] 

  -- logInfo m!"not flat:"
  -- go tree
  -- logInfo m!"flat:"
  -- go flattree



  

example :
  testTreeBind =
  (((F 1).bind fun x => (F (x.add 10)).bind fun y => some y).bind fun __do_lift =>
    (F (__do_lift.add 100)).bind fun y =>
      ((F 1000).bind fun x => (F (x.add 10000)).bind fun y => some y).bind fun __do_lift =>
        (F (__do_lift.add 100000)).bind fun z => some (y.add z))
:=
  rfl
  -- by
  -- unfold testTreeBind
  -- unfold_projs

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
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTestByName ``testTreeBind

def exex' : Option ℕ := do
  let z ← F 2
  let x ← H 4
  let y ← (do let x ← G (x + z); let y ← G x; H (x + z))
  H y
#check @Option.bind_assoc
set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTestByName ``exex'

def exex'' : Option ℕ := do
  let z ← F 2
  let x ← #v[1, 2, 3, 4].mapM (fun _ ↦ pure 4)
  let y ← (do let x ← G x[0]; let y ← G x; H (x + z))
  H y

#check @Option.bind_assoc
set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval runTestByName ``exex''

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
-- #eval runTestByName ``eboom

end NewTraversal

namespace ExampruSym
