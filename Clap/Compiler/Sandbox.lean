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
partial def walkAndShareCommon (e : Expr) : SymM Unit :=
  match e with
  | .lam .. => do
    Meta.lambdaTelescope e fun _xs b => do
      let _ ← Sym.shareCommon b
      walkAndShareCommon b
  | .app .. => do
    walkAndShareCommon e.getAppFn
    for a in e.getAppArgs do walkAndShareCommon a
  | _ => pure ()

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

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
#eval show MetaM Unit from do
  for n in [10, 20, 40, 80, 160, 320] do
    SymShareCommonMWE.bench n

opaque f : Nat → Option Nat

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
  rw [bind_assoc]
  rw [Option.bind_eq_bind]
  rw [bind_assoc]
