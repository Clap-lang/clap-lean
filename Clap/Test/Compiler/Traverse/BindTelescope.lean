import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Lean Meta Sym

opaque eq0 : Nat → Option Unit

private def natType : Expr := mkConst ``Nat

/-- `Vector Nat n` as a Core `Expr`. -/
def mkVecType (n : Nat) : Expr :=
  mkApp2 (mkConst ``Vector [0]) natType (mkNatLit n)

/-- `(v[i] : Nat)` where `v : Vector Nat n` and `i < n` (bounds proof via `sorry`,
matching the `sorry` the original example uses for the size proof). -/
def mkVecGet (v : Expr) (n i : Nat) : MetaM Expr := do
  let vecTy ← inferType v
  let natLT ← synthInstance (mkApp (mkConst ``LT [0]) natType)
  let ltBody := mkApp4 (mkConst ``LT.lt [0]) natType natLT (Expr.bvar 0) (mkNatLit n)
  let dom := Expr.lam `_xs vecTy (Expr.lam `i natType ltBody .default) .default
  let getElemTy := mkApp4 (mkConst ``GetElem [0, 0, 0]) vecTy natType natType dom
  let inst ← synthInstance getElemTy
  let proofTy := mkApp4 (mkConst ``LT.lt [0]) natType natLT (mkNatLit i) (mkNatLit n)
  let proof ← mkSorry proofTy (synthetic := false)
  return mkApp8 (mkConst ``GetElem.getElem [0, 0, 0])
    vecTy natType natType dom inst v (mkNatLit i) proof

/-- `(pure x : Option α)` (uses `Pure.pure` so that `Option.pure_apply` is the
relevant rewrite). -/
def mkOptionPure (αExpr x : Expr) : MetaM Expr :=
  mkAppOptM ``Pure.pure
    #[some (mkConst ``Option [0]), none, some αExpr, some x]

/-- Build the chain
`(pure (vec[0]+1) : Option _).bind fun row_0 => …
   (pure (vec[n-1]+1) : Option _).bind fun row_{n-1} =>
   some (Vector.mk { toList := [row_0, …, row_{n-1}] } sorry)`. -/
def buildChain (vec : Expr) (n : Nat) : MetaM Expr := do
  let rowDecls : Array (Name × (Array Expr → MetaM Expr)) :=
    (List.range n).toArray.map fun i =>
      (Name.mkSimple s!"row_{i}", fun _ => pure natType)
  withLocalDeclsD rowDecls fun rows => do
    let nilNat := mkApp (mkConst ``List.nil [0]) natType
    let listOfRows := rows.foldr (init := nilNat) fun r acc =>
      mkApp3 (mkConst ``List.cons [0]) natType r acc
    let arr := mkApp2 (mkConst ``Array.mk [0]) natType listOfRows
    let sizeEq ← mkEq (← mkAppM ``Array.size #[arr]) (mkNatLit n)
    let sizeProof ← mkSorry sizeEq (synthetic := false)
    let vector := mkApp4 (mkConst ``Vector.mk [0]) natType (mkNatLit n) arr sizeProof
    let sum ← mkAppM ``Vector.sum #[vector]
    let mut e ← mkAppM ``Option.some #[sum]
    for i in (List.range n).reverse do
      let body ← mkLambdaFVars #[rows[i]!] e
      let elem ← mkVecGet vec n i
      let plus1 ← mkAppM ``HAdd.hAdd #[elem, mkNatLit 1]
      let pureCall ← mkOptionPure natType plus1
      e ← mkAppM ``Option.bind #[pureCall, body]

    return e

abbrev vector (n: ℕ) : Vector Nat n := Vector.range n
#check Option.bind_some
/-- Build the full goal `<chain>.bind (fun x : Vector Nat n => eq0 x[0]) = sorry`
in a local context containing `vec : Vector Nat n`. Returns the goal mvar. -/
def chainTest (n : ℕ) : MetaM Unit := do
  -- let chain ← withLocalDeclD `vec (mkVecType n) fun vec => do
  let chain ← buildChain ((Expr.const ``ExampruSym.NewTraversal.vector []).beta #[mkNatLit n]) n
  logInfo m!"{chain}"
  runTest chain

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option trace.Clap.Compile true
#eval chainTest 320

/-
Compilation times
OLD
chainTest   1 -  0.002s
chainTest   2 -  0.003s
chainTest   3 -  0.002s
chainTest   4 -  0.004s
chainTest   5 -  0.005s
chainTest   6 -  0.005s
chainTest   7 -  0.005s
chainTest   8 -  0.006s
chainTest   9 -  0.007s
chainTest  10 -  0.008s
chainTest  20 -  0.021s
chainTest  40 -  0.061s
chainTest  80 -  0.205s
chainTest 160 -  0.883s
chainTest 320 -  4.228s - maxRecDepth
chainTest 640 - 30.692s - heartbeats
NEW
chainTest  10  - 0.005s
chainTest  20  - 0.005s
chainTest  40  - 0.008s
chainTest  80  - 0.014s
chainTest 160  - 0.033s
chainTest 320  - 0.087s
chainTest 640  - 0.024s
chainTest 1280 - 0.782s - something other than compilation takes several seconds here
-/


end NewTraversal

end ExampruSym
