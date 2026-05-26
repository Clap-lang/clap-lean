import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

open SymSets Monad General Vector

def exex : Option Unit :=
  Option.bind (eq0 4) fun _ : Unit ↦
    Option.bind
      ((Option.bind
         (Option.bind
           (Option.bind
             (F 2) fun x ↦
            Option.bind (F 3) fun y ↦ G (x + y))
           fun x ↦ H x))
         fun x ↦ F x) fun x ↦
      F x

#print exex

namespace NewTraversal

def testInnerReturn : Option Unit := do
  let x ← F 1
  let y ← F (←(fun (x: ℕ) => do
    return x) 3)
  let z ← F 3
  pure ()

set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval spoon <| do
  let e ← compileExample ``testInnerReturn (←(mapM_singlePass_pre))
  -- Pretty print (i.e. go back to `Bind.bind`)
  return (←Sym.simp e (←compilerBindEqBind)).getResultExpr e


def exex' : Option Unit := do
  let z ← F 2
  let x ← H 4
  let y ← (do let x ← G (x + z); let y ← G x; H (x + z))
  H y

def exex'' : Option Unit := do
  let z ← F 2
  let x ← #v[1, 2].mapM (fun _ ↦ pure 4)
  let y ← (do let x ← G x[1]; let y ← G x; H (x + z))
  H y

#check @Option.bind_assoc

set_option trace.Clap.Compile true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
#eval spoon <| do
  let e ← compileExample ``exex'' (←(mapM_singlePass_pre))
  -- Pretty print (i.e. go back to `Bind.bind`)
  return (←Sym.simp e (←compilerBindEqBind)).getResultExpr e

end NewTraversal

#exit

-- set_option maxRecDepth 500000
-- set_option trace.Clap.Compile true

def ex₀ : Option Unit := do
  eq0 0
  eq0 1
  let _res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 2)
  eq0 3
  return ()

/--
info: Compiled:
do
  eq0 0
  eq0 1
  do
    eq0 2
    let init ← eq0 2
    some init
  eq0 3
  some PUnit.unit
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval do spoon (compileExampleJustSym ``ex₀ (←(foldlM ∪ monads)))

set_option trace.Clap.Compile true in
#eval do spoon (compileExample ``ex₀ (←(foldlM)))

-- mkPostMethodsSinglePass

def ex₁ (_vec : Vector Nat 3) : Option Unit := do
  eq0 #v[4, 5][0]

/--
info: Compiled:
fun _vec => eq0 4
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁ (←getElem)

set_option trace.Clap.Compile true in
#eval spoon <| do compileExample ``ex₁ (←getElem)

/--
info: Compiled:
fun _vec => eq0 4
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExample ``ex₁ (←getElem)

def ex₂ (vec : Vector Nat 160) : Option Unit := do
  let x := (vec ++ vec)[0] -- `GetElem (Vector _ (3 + 3))`
  eq0 x
-- /--
-- info: Compiled:
-- fun vec => eq0 vec[0]
-- -/
-- #guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₂ (←(getElem ∪ append ∪ zeta ∪ explode))

def ex₃ (vec : Vector Nat 200) : Option Unit := do
  let x := vec.map (·+1)
  eq0 x[0]

/--
info: Compiled:
fun vec => eq0 (vec[0] + 1)
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₃ (←(map ∪ zeta ∪ getElem ∪ explode))

def ex₄ (vec : Vector Nat 5) : Option Unit :=
  vec.mapM (fun x ↦ Option.some <| x + 1) |>.bind fun x ↦ eq0 x[0]

-- -- /--
-- -- info: Compiled:
-- -- fun vec => eq0 (vec[0] + 1)
-- -- -/
-- -- #guard_msgs(info, whitespace := lax, drop warning) in
-- set_option pp.exprSizes true in
-- -- set_option trace.Clap.Compile true in
-- set_option trace.Clap.Compile.simp.proc.vector_mapM_mk true in
-- set_option trace.profiler true in
-- set_option profiler true in
-- set_option trace.Clap.Compile true in
set_option trace.Clap.Compile true in
#eval spoon <| do
  compileExampleJustSym ``ex₄
    (←(mapM_alt ∪ monads ∪ getElem ∪ explode ∪ bindMyAssoc_set ∪ append))

def profileThis := spoon <| do compileExampleJustSym ``ex₄ (←(mapM ∪ monads ∪ getElem))

def reportAttempt : Sym.Simp.Simproc := fun e ↦ do
  discard bump
  return .rfl

def reportSet : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``reportAttempt
  ]


def ex₅ (vec : Vector Nat 10) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := vec.zipWith (bs := vec.map (·+1)) fun x y ↦ x + y
  eq0 res[0]
  eq0 res[1]
  eq0 res[2]

set_option trace.Clap.Compile true in
set_option maxRecDepth 100000 in
-- /--
-- info: Compiled:
-- fun vec =>
--   (eq0 vec[0]).bind fun x =>
--     (eq0 0).bind fun x =>
--       (eq0 (vec[0] + (vec[0] + 1))).bind fun x =>
--         (eq0 (vec[1] + (vec[1] + 1))).bind fun x => eq0 (vec[2] + (vec[2] + 1))
-- -/
-- #guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do
  let res ← compileExampleJustSym
    ``ex₅
    (←(reportSet ∪ append ∪ explode ∪ getElem ∪ map ∪ zipWith ∪ zeta ∪ monads))
  logInfo m!"this many times: {←getCounter}"
  return res


def ex₆ (vec : Vector Nat 160) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := (vec.drop 1).take 1
  eq0 res[0]

/--
info: Compiled:
fun vec => (eq0 vec[0]).bind fun x => (eq0 0).bind fun x => eq0 vec[1]
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₆ (←(append ∪ getElem ∪ drop ∪ take ∪ zeta ∪ monads ∪ explode))

-- `f (λ f (λ g #1 #0))`
-- `[0:#1, 1:#0, 2:g, 3: 2 1, 4: 3 1, 5: λ 4, 6: f, 7: λ 6 5, 8: 6 7]`
-- `f ==> f'`
-- `[0:#1, 1:#0, 2:g, 3: 2 1, 4: 3 1, 5: λ 4, 6: f, 7: λ 6 5, 8: 6 7, 9: f']`
--

def ex₇ (vec : Vector Nat 3) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := vec.sum
  eq0 res

-- def compile (e : Expr) : (Expr, Name) :=
--   match_expr e with
--   | Option.bind _ _ a f =>
--     match_expr a with
--     | Option.some _ x =>
--       let e' : Expr := f.beta #[x]
--       (e', ``LawfulMonad.bind_some)
--     | _ => e
--   | _ => e

-- set_option trace.Clap.Compile true
-- -- /--
-- -- info: Compiled:
-- -- fun vec =>
-- -- (eq0 vec[0]).bind fun x =>
-- -- (eq0 0).bind fun x =>
-- -- eq0 (vec[0] + (vec[1] + (vec[2] + 0)))
-- -- -/
-- #guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₇ (←(append ∪ getElem ∪ sum ∪ zeta ∪ monads ∪ explode))

def ex₈ (n : ℕ) (vec : Vector Nat n) : Option Unit := do
  let x ← (do let _ ← eq0 2; let X ← vec.mapM (fun x ↦ (eq0 (x + 42) : Option _)); return 4)
  eq0 x

def ex₈_fixed (vec : Vector Nat 2) : Option Unit := do
  let x ← (do let _ ← eq0 2; let X ← vec.mapM (fun x ↦ (eq0 (x + 42) : Option _)); return 4)
  eq0 x

  -- let res ← vec.mapM (fun n ↦ return n + 1)
  -- eq0 res[0]
  -- let y ← (do eq0 4; let y ← pure 4; let z ← #v[1, 2].mapM (return·+42); eq0 z[0]; return y)
  -- let z := (List.range y)[0]'sorry
  -- eq0 res[1]
  -- eq0 res[2]

-- def ex₈' (vec : Vector Nat 100) : Option Unit := do
--   let x ← (do let _ ← eq0 2; let _ ← vec.foldlM (fun acc x ↦ (eq0 (x + 42) : Option _)) (()); return 4)
--   eq0 x
--   -- let res ← vec.mapM (fun n ↦ return n + 1)
--   -- eq0 res[0]
--   -- let y ← (do eq0 4; let y ← pure 4; let z ← #v[1, 2].mapM (return·+42); eq0 z[0]; return y)
--   -- let z := (List.range y)[0]'sorry
--   -- eq0 res[1]
--   -- eq0 res[2]
#check bind_assoc
set_option pp.exprSizes true in
set_option trace.Clap.Compile true in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
-- set_option pp.exprSizes true in
-- /--
-- info: Compiled:
-- fun vec =>
--   (eq0 42).bind fun x =>
--     (eq0 (vec[0] + 1 + 1)).bind fun x =>
--       ((eq0 4).bind fun x => (eq0 (1 + 42)).bind fun x => some 4).bind fun y =>
--         (eq0 (vec[1] + 5 + 1)).bind fun x => eq0 (vec[2] + 10 + 1)
-- -/
-- #guard_msgs(info, whitespace := lax, drop warning) in

#eval spoon <| do
  let (e, time) ← Dbg.timeS <| compileExampleJustSym ``ex₈_fixed
    (←(reportSet ∪ mapM_alt ∪ zeta ∪ monads ∪ explode
    -- ∪ compilerAssoc
    ∪ bindMyAssoc_set
    -- mapM_alt
    ))
  logInfo m!"Compilation took: {time}s"
  -- logInfo m!"this many times: {←getCounter}"
  -- Pretty print (i.e. go back to `Bind.bind`)
  return (←Sym.simp e (←compilerBindEqBind)).getResultExpr e

-- def xx : MetaM Sym.Simp.Methods :=

-- set_option trace.Clap.Compile.dbg true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile true in
-- #eval spoon <| do
--   resetDbgState
--   let e ← compileExample (args := #[toExpr 160]) ``ex₈
--     (←(mapM_singlePass ∪ zeta ∪ monads ∪ explode
--     -- ∪ compilerAssoc
--     -- ∪ bindMyAssoc_set
--     -- mapM_alt
--     ))
--   let σ ← getDbgState
--   logInfo m!"σ: {repr σ}"

--   return e
--   -- Pretty print (i.e. go back to `Bind.bind`)
--   -- return (←Sym.simp e (←compilerBindEqBind)).getResultExpr e

set_option maxRecDepth 1024 in
set_option trace.Clap.Compile.dbg true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile false in
#eval do
  let (e, time) ← Dbg.timeS <| compileExample (args := #[toExpr 5]) ``ex₈
    (←(SymSets.Vector.wrapped ∪
      mapM_singlePass_pre ∪
      explode -- ∪ zeta ∪ monads ∪ explode
    -- ∪ compilerAssoc
    ∪ bindMyAssoc_set
    -- mapM_alt
    )) |>.run' {} |>.run
  logInfo m!"time: {time}"
  let e' := Sym.simp e (←compilerBindEqBind)
  let e' ← e'.run

  logInfo m!"e: {e'.getResultExpr e}"
  logInfo m!"{←(getAndResetDbgState <&> repr)}"
  -- return e

-- set_option trace.Clap.Compile true
-- set_option trace.Clap.Compile.up true
set_option Clap.traversalDbg true
set_option trace.Clap.Compile.dbg false
def bench : MetaM Unit := do
  let simpset := (←(SymSets.Vector.wrapped ∪ mapM_singlePass_pre ∪ explode ∪ compilerAssoc))
  -- let simpset := (←(mapM_singlePass ∪ zeta ∪ explode))
  let inputSizes := (Array.range 2).map (10 * 2^·)
  let timings ← inputSizes.mapM fun inputSize ↦ do
    let res ← Dbg.timeS <| (compileExample ``ex₈ simpset (args := #[mkNatLit inputSize])).run' {} |>.run
    let σ ← getAndResetDbgState
    return (inputSize, res, σ)
  for (n, (compiled, time), dbgState) in timings do
    logInfo m!"ex₈[{n}] took {time}s"
    logInfo m!"dbg: {repr dbgState}"

    logInfo m!"{←ppMonad compiled}"
    -- logInfo m!"res:\n{(←Sym.simp compiled (←compilerBindEqBind) |>.run).getResultExpr compiled}"

  -- for n in inputSizes do
  --   let (res, time) ← Dbg.timeS ∘ spoon <|
  --     compileExample ``ex₈ (←(mapM_singlePass ∪ zeta ∪ monads ∪ explode ∪ bindMyAssoc_set))
  --   timings := timings.push time
  --   logInfo m!"res:\n{res}"
  -- for timing in timings do

set_option maxRecDepth 40000 in
#eval bench

-- 10 vec, [size 1409/272/272] of compiled
opaque share : Nat → Option Nat

def ex₉ {n : Nat} (vec : Vector Nat n) : Option Unit := do
  let x ← (do let _ ← eq0 2; let x ← vec.mapM (fun x ↦ (share (x + 42) : Option _)); return x)
  let _ ← x.mapM eq0

set_option maxRecDepth 1024 in
set_option trace.Clap.Compile.dbg true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile false in
#eval do
  let (e, time) ← Dbg.timeS <| compileExample (args := #[toExpr 20]) ``ex₉
    (←(SymSets.Vector.wrapped ∪
      mapM_singlePass_pre ∪
      getElem ∪
      append ∪
      explode -- ∪ zeta ∪ monads ∪ explode
    ∪ compilerAssoc
    -- ∪ bindMyAssoc_set
    -- mapM_alt
    )) |>.run' {} |>.run
  logInfo m!"time: {time}"
  -- let e' := Sym.simp e {}
  let e' := Sym.simp e (←compilerBindEqBind)
  let e' ← e'.run

  logInfo m!"e: {e'.getResultExpr e}"
  logInfo m!"{←(getAndResetDbgState <&> repr)}"

set_option trace.Clap.Compile true in
#eval spoon <| do
  let e ← compileExampleJustSym ``ex₉
    (←(mapM_alt ∪ zeta ∪ monads ∪ explode ∪ getElem ∪ append
    -- ∪ compilerAssoc
    ∪ bindMyAssoc_set
    -- mapM_alt
    ))
  -- Pretty print (i.e. go back to `Bind.bind`)
  return (←Sym.simp e (←compilerBindEqBind)).getResultExpr e

-- set_option trace.Clap.Compile true in
-- example {vec : Vector Nat 10} : ex₈ vec = .none := by
--   unfold ex₈

--   cbv
--   -- compile_just_sym [SymSets.Vector.mapM]
  -- rw [Option.bind_eq_bind]
  -- rw [Option.bind_eq_bind]
  -- -- rw [Option.bind_assoc]
  -- compile_just_sym [compilerBindEqBind]
  -- rw [bind_assoc]
  -- rw [bind_assoc]
  -- rw [bind_assoc]


  -- compile_just_sym [compilerAssoc]
  -- rw [bind_assoc]

  -- #check bind_assoc
-- set_option trace.Clap.Compile true in
-- example {vec : Vector Nat 10} : ex₈' vec = sorry := by
--   unfold ex₈'
--   compile_just_sym [SymSets.Vector.foldlM, explode]
--   rw [Option.bind_eq_bind]
--   rw [Option.bind_eq_bind]
--   compile_just_sym [compilerAssoc]
--   compile_just_sym [compilerBindEqBind]

-- def ex₈' (vec : Vector Nat 3) : Option Unit := do
--   let x ← (do let _ )

def ex₉ (vec : Vector Nat 160) : Option Unit := do
  let res := (#v[0] ++ vec).extract 1 2
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 vec[0]
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₉ (←(extract ∪ append ∪ getElem ∪ zeta ∪ monads ∪ explode))

def ex₁₀ (vec : Vector Nat 160) : Option Unit := do
  let res := (#v[0] ++ vec).set 0 42
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 42
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁₀ (←(set ∪ append ∪ getElem ∪ zeta ∪ monads ∪ explode))

def ex₁₁ (vec : Vector Nat 160) : Option Unit := do
  let res := vec.mapIdx fun i x ↦ x + i
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 (vec[0] + 0)
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁₁ (←(mapIdx ∪ getElem ∪ zeta ∪ monads ∪ explode))

-- def mixLast {t : ℕ} (state : Vector (F p) t) (M : Vector (Vector (F p) t) t) (s : ℕ) : F p :=
--   (state.zipWith (fun (sj : F p) (row : Vector (F p) t) ↦ row[s]'sorry * sj) M).sum

def ex₁₂ (vec : Vector Nat 4) : Option Unit := do
  let state : Vector Nat 2 := #v[1, 2]
  let M : Vector (Vector ℕ 2) 2 := #v[#v[1, 2], #v[3, 4]]
  let res :=
    (state.zipWith (fun (sj : ℕ) (row : Vector ℕ 2) ↦ row[0]'sorry * sj) M).sum
  eq0 res

/--
info: Compiled:
fun vec => eq0 7
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁₂ (←(zeta ∪ monads ∪ explode ∪ zipWith ∪ sum ∪ getElem))
def ex₁₃ (vec : Vector Nat 4) : Option Unit := do
  let t := 2
  let state : Vector Nat t := #v[1, 2]
  let S : Vector Nat 6 := #v[3, 4, 5, 6, 7, 8]
  let base : ℕ := (2 * 2 - 1) * 1
  let s' : Vector _ t := ⟨S.extract base (base+t) |>.toArray, sorry⟩
  let dotProduct := (state.zipWith (· * ·) s').sum
  let tail := (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]'sorry * S[base + t + i]'sorry)
  let res : Vector Nat 2 := ⟨#[dotProduct] ++ tail.toArray, sorry⟩
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 20
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do
  compileExampleJustSym ``ex₁₃
    (←(zeta ∪ monads ∪ explode ∪ zipWith ∪ sum ∪ extract ∪ toArray ∪ mapIdx ∪ append ∪ getElem ∪ drop ∪ extract))

opaque p : Nat
opaque q : Nat
axiom a : p = q
def test := fun x : Nat => (x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x)
set_option pp.exprSizes true in
set_option maxRecDepth 1000 in
example : (fun x : Nat => (x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x)) p = sorry := by
  sym_simp [beta]

opaque f : (Nat → Nat) → Nat
def exp := fun x : Nat ↦ f (fun x : Nat ↦ f (fun _ : Nat ↦ 0))

def abc : Sym.SymM Unit := do
  let expr := (←getEnv).find? ``Clap.Compiler.ExampruSym.exp |>.get!.value!
  let s := (← get).share.set.toList
  logInfo m!"{s.map (·.expr)}"
  let e ← Sym.shareCommon expr
  let s := (← get).share.set.toList
  logInfo m!"{s.map (·.expr)}"

#eval abc.run

end ExampruSym
