-- import Lean
-- import Lean.Meta.Sym.Simp.Debug

-- /-!
-- Programmatic replacement for the previous elaboration-heavy `sym_simp`
-- exerciser. Builds the Core `Expr` for the same goal the original example
-- produced after elaboration:

--   (do let x : Vector Nat n ←
--         (pure (vec[0] + 1) : Option Nat).bind fun row_0 =>
--         …
--         (pure (vec[n-1] + 1) : Option Nat).bind fun row_{n-1} =>
--         some (Vector.mk { toList := [row_0, …, row_{n-1}] } sorry)
--       eq0 x[0]) = sorry

-- then runs `Sym.simpGoal [Option.pure_apply]` on a fresh metavariable with
-- that type. Style follows `tests/elab_bench/cbv_leroy.lean`.
-- -/

-- set_option autoImplicit true

-- open Lean Meta Sym

-- opaque eq0 : Nat → Option Unit

-- namespace SymSimpDoBench

-- private def natType : Expr := mkConst ``Nat

-- /-- `Vector Nat n` as a Core `Expr`. -/
-- def mkVecType (n : Nat) : Expr :=
--   mkApp2 (mkConst ``Vector [0]) natType (mkNatLit n)

-- /-- `(v[i] : Nat)` where `v : Vector Nat n` and `i < n` (bounds proof via `sorry`,
-- matching the `sorry` the original example uses for the size proof). -/
-- def mkVecGet (v : Expr) (n i : Nat) : MetaM Expr := do
--   let vecTy ← inferType v
--   let natLT ← synthInstance (mkApp (mkConst ``LT [0]) natType)
--   let ltBody := mkApp4 (mkConst ``LT.lt [0]) natType natLT (Expr.bvar 0) (mkNatLit n)
--   let dom := Expr.lam `_xs vecTy (Expr.lam `i natType ltBody .default) .default
--   let getElemTy := mkApp4 (mkConst ``GetElem [0, 0, 0]) vecTy natType natType dom
--   let inst ← synthInstance getElemTy
--   let proofTy := mkApp4 (mkConst ``LT.lt [0]) natType natLT (mkNatLit i) (mkNatLit n)
--   let proof ← mkSorry proofTy (synthetic := false)
--   return mkApp8 (mkConst ``GetElem.getElem [0, 0, 0])
--     vecTy natType natType dom inst v (mkNatLit i) proof

-- /-- `(pure x : Option α)` (uses `Pure.pure` so that `Option.pure_apply` is the
-- relevant rewrite). -/
-- def mkOptionPure (αExpr x : Expr) : MetaM Expr :=
--   mkAppOptM ``Pure.pure
--     #[some (mkConst ``Option [0]), none, some αExpr, some x]

-- /-- Build the chain
-- `(pure (vec[0]+1) : Option _).bind fun row_0 => …
--    (pure (vec[n-1]+1) : Option _).bind fun row_{n-1} =>
--    some (Vector.mk { toList := [row_0, …, row_{n-1}] } sorry)`. -/
-- def buildChain (vec : Expr) (n : Nat) : MetaM Expr := do
--   let rowDecls : Array (Name × (Array Expr → MetaM Expr)) :=
--     (List.range n).toArray.map fun i =>
--       (Name.mkSimple s!"row_{i}", fun _ => pure natType)
--   withLocalDeclsD rowDecls fun rows => do
--     let nilNat := mkApp (mkConst ``List.nil [0]) natType
--     let listOfRows := rows.foldr (init := nilNat) fun r acc =>
--       mkApp3 (mkConst ``List.cons [0]) natType r acc
--     let arr := mkApp2 (mkConst ``Array.mk [0]) natType listOfRows
--     let sizeEq ← mkEq (← mkAppM ``Array.size #[arr]) (mkNatLit n)
--     let sizeProof ← mkSorry sizeEq (synthetic := false)
--     let vector := mkApp4 (mkConst ``Vector.mk [0]) natType (mkNatLit n) arr sizeProof
--     let mut e ← mkAppM ``Option.some #[vector]
--     for i in (List.range n).reverse do
--       let body ← mkLambdaFVars #[rows[i]!] e
--       let elem ← mkVecGet vec n i
--       let plus1 ← mkAppM ``HAdd.hAdd #[elem, mkNatLit 1]
--       let pureCall ← mkOptionPure natType plus1
--       e ← mkAppM ``Option.bind #[pureCall, body]
--     return e

-- /-- Build the full goal `<chain>.bind (fun x : Vector Nat n => eq0 x[0]) = sorry`
-- in a local context containing `vec : Vector Nat n`. Returns the goal mvar. -/
-- def mkBenchGoal (n : Nat) (k : MVarId → MetaM α) : MetaM α := do
--   withLocalDeclD `vec (mkVecType n) fun vec => do
--     let chain ← buildChain vec n
--     let lam ← withLocalDeclD `x (mkVecType n) fun x => do
--       let elem ← mkVecGet x n 0
--       let body ← mkAppM ``eq0 #[elem]
--       mkLambdaFVars #[x] body
--     let outer ← mkAppM ``Option.bind #[chain, lam]
--     let rhs ← mkSorry (← inferType outer) (synthetic := false)
--     let goalType ← mkAppM ``Eq #[outer, rhs]
--     let mvar ← mkFreshExprSyntheticOpaqueMVar goalType
--     k mvar.mvarId!

-- /-- Build the goal at size `n`, run `Sym.simpGoal [Option.pure_apply]`, and print
-- wall-clock time spent in `preprocessMVar` + `simpGoal`. -/
-- def runBench (n : Nat) : MetaM Unit := mkBenchGoal n fun mvarId => do
--   let methods ← mkMethods #[``Option.pure_apply]
--   let config : Sym.Simp.Config := { maxSteps := 10_000_000 }
--   let startMs ← IO.monoMsNow
--   let _ ← SymM.run do
--     let mvarId ← preprocessMVar mvarId
--     (← simpGoal mvarId methods config).toOption
--   let endMs ← IO.monoMsNow
--   let secs := (Float.ofNat (endMs - startMs)) / 1000.0
--   IO.println s!"sym_simp(n={n}): {secs}s"

-- def runBenches : MetaM Unit := do
--   for n in [10, 20, 40, 80, 160] do runBench n

-- end SymSimpDoBench

-- set_option maxHeartbeats 0 in
-- set_option maxRecDepth 4000 in
-- #eval SymSimpDoBench.runBenches

import Lean
import Lean.Meta.Sym.Simp.Debug

/-!
MWE for the `Sym.shareCommon` hot path uncovered by profiling
`sym_simp_option_bind_bench.lean`.

`Sym.Simp.simpLambda'` (`src/Lean/Meta/Sym/Simp/Lambda.lean:48-58`) calls
`Sym.shareCommon` once on the lambda body when it enters, and again on the
rebuilt lambda when it leaves. `Sym.shareCommon` (`SymM.lean:252`) is the
non-incremental variant: it builds a fresh local pointer map and walks the
whole body, checking each subterm against a global `PHashSet`.

For a do-block of `n` `bind`s the body of each lambda still has size
O(n - i), so the total work across all lambda levels is Θ(n²). Combined
with simp's recursive descent into the chain, this is the dominant cost
(≈41% of `sym_simp_option_bind_bench` at n=160 in the samply profile).

This file removes the rewrites and the `Vector.mk` payload to show the
quadratic call pattern in isolation.
-/

/-
This is Sebastian Graf's example.
-/

open Lean Meta Sym

def Lean.Meta.Sym.AlphaShareCommon.State.printMe (m : AlphaShareCommon.State) : MetaM Unit := do
  logInfo m!"----------PRINTME----------"
  let m := m.set.toList.mergeSort
    (le := fun e₁ e₂ ↦ e₁.expr.sizeWithoutSharing ≤ e₂.expr.sizeWithoutSharing) |>.map (·.expr)
  logInfo m!"Len: {m.length}"
  let m ← m.mapM PrettyPrinter.ppExpr
  let m := m.map (·.pretty)
  let m := String.intercalate ", " m
  logInfo m!"Map: {m}"
  logInfo m!"----------THE FIN----------"

  -- m.forM fun elem ↦ plogInfo (m!"{m}")

namespace SymShareCommonMWE

private def natType : Expr := mkConst ``Nat
private def nilNat : Expr := mkApp (mkConst ``List.nil [0]) natType

/-- Opaque combinator so the chain has an interleaved application between
each lambda; the binders aren't contiguous, so each level is its own
`simpLambda'` step rather than one big `lambdaTelescope`. -/
opaque f : (Nat → List Nat) → List Nat

/-- Build `f (fun a₀ => f (fun a₁ => … f (fun a_{n-1} => [a₀, a₁, …, a_{n-1}])))`
where the innermost `List.cons` chain references every bound variable. -/
def buildChain (n : Nat) : MetaM Expr := do
  let names : Array (Name × (Array Expr → MetaM Expr)) :=
    (List.range n).toArray.map fun i => (Name.mkSimple s!"a_{i}", fun _ => pure natType)
  withLocalDeclsD names fun fvs => do
    let list := fvs.foldr (init := nilNat) fun fv acc =>
      mkApp3 (mkConst ``List.cons [0]) natType fv acc
    -- fold outward: outermost binder is `a_0`
    let mut body := list
    for i in (List.range n).reverse do
      let lam ← mkLambdaFVars #[fvs[i]!] body
      -- wrap in `f (…)` so each lambda sits under a fresh application
      body ← mkAppM ``f #[lam]
    return body

/-- Walk every lambda subterm; at each `.lam`, open it with `lambdaTelescope`
and call `Sym.shareCommon` on the body. This is the exact pattern of
`Sym.Simp.simpLambda'` (minus the rewriting). -/
partial def walkAndShareCommon (e : Expr) : SymM Unit := do
  logInfo m!"walkAndShareCommon[{e}]:"
  (←get).share.printMe
  match e with
  | .lam .. => do
    logInfo m!"[.lam]"
    Meta.lambdaTelescope e fun _xs b => do
      let _ ← Sym.shareCommon b
      walkAndShareCommon b
  | .app .. => do
    logInfo m!"[.app]"
    walkAndShareCommon e.getAppFn
    for a in e.getAppArgs do
      logInfo m!"[arg]"
      walkAndShareCommon a
  | _ =>
    logInfo m!"[_]"
    pure ()

def timeMs {α} (k : MetaM α) : MetaM (α × Float) := do
  let s ← IO.monoNanosNow
  let a ← k
  let e ← IO.monoNanosNow
  return (a, (e - s).toFloat / 1e6)

def bench (n : Nat) : MetaM Unit := do
  let e ← buildChain n
  let (_, single) ← timeMs <| SymM.run (Sym.shareCommon e)
  let (_, walk) ← timeMs <| SymM.run (walkAndShareCommon e)
  IO.println s!"n={n}  single shareCommon: {single}ms   per-lambda walk: {walk}ms"

end SymShareCommonMWE

-- set_option maxHeartbeats 0 in
-- set_option maxRecDepth 4000 in
-- #eval show MetaM Unit from do
--   for n in [10] do
--   -- for n in [10, 20, 40, 80, 160, 320] do
--     SymShareCommonMWE.bench n

opaque f : Nat → Option Nat
set_option pp.notation false in
#check bind_assoc
def g : Option Unit := do
  let y ← (do let x ← f 4
              let x ← f x
              let y ← f x
              .some y
          )
  let x ← .some 43
  let z ← f y
  discard (f x)
  discard (f z)
  return ()

example : g = sorry := by
  unfold g
  simp only [bind_assoc]
  
  simp only [Option.bind_eq_bind]
  unfold Option.bind

  rw [bind_assoc]
  rw [Option.bind_eq_bind]
  rw [bind_assoc]
