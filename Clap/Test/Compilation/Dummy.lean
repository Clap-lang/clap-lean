import Clap.Spec
import Clap.Compiler.Cimplol

open Clap Spec Compiler

-- set_option debug.skipKernelTC true
-- set_option maxRecDepth 1000000
-- set_option maxHeartbeats 800000
-- set_option trace.Clap.Compiler true
-- set_option trace.Clap.Compiler.preprocess true
-- set_option profiler true
-- set_option profiler.threshold 0

abbrev p := Primes.bn254

def mixS (n : ℕ) (r:ℕ) (x : Vector (ZMod p) n) : Option (Vector (ZMod p) n) := do
  eq0 (x[0]! + (List.range' (800 * r) 800).sum : ZMod p)
  x

def poseidon (n:ℕ) (x : Vector (ZMod p) n) : Option (ZMod p) := do
  let state ← (List.range 4).foldlM (fun state r ↦ mixS (n := n) r state) (init:=x)
  state.sum

def keyless (x : Vector (ZMod p) 2) (y : Vector (ZMod p) 4) : Option Unit := do
  let x ← poseidon _ x
  let y ← poseidon _ y
  eq0 (x+y)
  eq0 [(1 : ZMod p),2,3].sum

open Lean Meta in
partial def unjustTraverse (name : Name) (args : Array Expr) (e : Expr) : MetaM Unit := do
  logInfo m!"Simplifying[{name} {String.intercalate " " (←args.mapM (fun x ↦ (PrettyPrinter.ppExpr x) <&> Format.pretty)).toList}]:\n{e}"
  let list := [`keyless, `poseidon, `mixS]
  discard <| Meta.transform (skipConstInApp := true) e
    -- (pre := fun e ↦ do
    --   if ←isTypeFormer e then return .done e
    --   if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e
    --   if e.isRawNatLit then return .continue
    --   logInfo m!"Pre: {e}"
    --   return .continue)
    (post := fun e ↦ do
      if ←isTypeFormer e then return .done e
      if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e
      if e.isRawNatLit then return .continue

      let (name, args) := e.getAppFnArgs
      if name == .anonymous then return .continue

      -- logInfo m!"name: {name}"

      if list.contains name then
        -- logInfo m!"in like Flynn: {name}"
        let isAllValid ← args.allM fun e ↦ do
          -- logInfo m!"arg: {e}"
          let_expr Vector _ n := ←inferType e |
            -- logInfo m!"NOT VECTOR"
            return true
          let reducedN ← Meta.reduce n
          if n != reducedN then
            logInfo m!"Reduction did something.\n{n}→{reducedN}"
          -- logInfo m!"reduced: {reducedN} -- isRawNatLit: {reducedN.isRawNatLit}"
          return reducedN.isRawNatLit
        
        if isAllValid then logInfo m!"Adding to map:\n{e} [hash={e.hash}]"
        -- logInfo m!"Args: {args}"
        let func := ((←getEnv).find? name).get!.value!
        let appliedFunc := func.instantiateLambdasOrApps args
        unjustTraverse name args appliedFunc
      -- logInfo m!"Post: {e}"
      return .continue)

open Lean in
run_meta do
  unjustTraverse `keyless #[.const `x [], .const `y []] ((←getEnv).find? `keyless).get!.value!
