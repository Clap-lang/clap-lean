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

def mixS (m n : ℕ) (r:ℕ) (x : Vector (ZMod p) n) (y : Vector (ZMod p) m) : Option (Vector (ZMod p) n) := do
  eq0 (x[0]! + (List.range' (800 * r) 800).sum : ZMod p)
  x

def poseidon (n:ℕ) (x : Vector (ZMod p) n) : Option (ZMod p) := do
  let state ← (List.range 4).foldlM (fun state r ↦ mixS (m := 0) (n := n) r state #v[]) (init:=x)
  state.sum

def keyless (x : Vector (ZMod p) 2) (y : Vector (ZMod p) 4) : Option Unit := do
  let x ← poseidon _ x
  let y ← poseidon _ y
  let z ← poseidon _ #v[(1 : ZMod p), 2, 3, 4]
  eq0 (x+y+z)
  eq0 [(1 : ZMod p),2,3].sum

open Lean Meta in
partial def unjustTraverse (name : Name) (args : Array Expr) (e : Expr) (σ : Std.HashMap UInt64 Expr := {}): MetaM Unit := do
  -- logInfo m!"Simplifying[{name} {String.intercalate " " (←args.mapM (fun x ↦ (PrettyPrinter.ppExpr x) <&> Format.pretty)).toList}]:\n{e}"
  let list := [`keyless, `poseidon, `mixS]
  discard <| Meta.transform (skipConstInApp := true) e
    -- (pre := fun e ↦ do
    --   if ←isTypeFormer e then return .done e
    --   if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e
    --   if e.isRawNatLit then return .continue
    --   logInfo m!"Pre: {e}"
    --   return .continue)
    (post := fun e ↦ do
      if σ.contains e.hash then logInfo m!"In cache:\n{e}"; return .done e -- .done σ[e.hash]!

      if ←isTypeFormer e then return .done e
      if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e
      if e.isRawNatLit then return .continue

      let (name, args) := e.getAppFnArgs
      if name == .anonymous then return .continue

      -- logInfo m!"name: {name}"

      if list.contains name then

        -- logInfo m!"Args: {args}"
        let func := ((←getEnv).find? name).get!.value!
        let funcT := ((←getEnv).find? name).get!.type

        -- Analyse the signature of `f`
        let vecLenIds ← forallTelescopeReducing funcT fun args _ ↦ do
          let mut res : FVarIdSet := {}
          for arg in args do
            let_expr Vector _ n := ←inferType arg | continue
            let fvars := collectFVars {} n |>.fvarSet
            res := res.union fvars
            logInfo m!"Collected fvars[{arg}]: {←fvars.toList.mapM (·.getUserName)}"
          logInfo m!"all fvars: {←res.toList.mapM (·.getUserName)}"
          return res

        -- logInfo m!"in like Flynn: {name}"
        -- Analyse the call site of `f`
        let isAllValid ← args.allM fun e ↦ do
          -- TODO(monaday): Here, go over all args, ensure they are ground _AND_
          -- accumulate based on `vecLenIds` the key to insert into the cache.
          -- logInfo m!"arg: {e}"
          let_expr Vector _ n := ←inferType e |
            -- logInfo m!"NOT VECTOR"
            return true

          let reducedN ← Meta.reduce n
          -- if n != reducedN then
          --   logInfo m!"Reduction did something.\n{n}→{reducedN}"
          -- logInfo m!"reduced: {reducedN} -- isRawNatLit: {reducedN.isRawNatLit}"
          return reducedN.isRawNatLit

        if isAllValid then
          -- assuming vector lengths are the first arguments
          let key := s!"{name} {args.take vecLenIds.size}"
          logInfo m!"Adding to map:\n{e} [hash={key.hash}]"

        let appliedFunc := func.instantiateLambdasOrApps args
        unjustTraverse name args appliedFunc
      -- logInfo m!"Post: {e}"
      return .continue)

open Lean in
run_meta do
  unjustTraverse `keyless #[.const `x [], .const `y []] ((←getEnv).find? `keyless).get!.value!
