import Clap.Spec
import Clap.Compiler.Reduce

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
  let z ← poseidon _ #v[(1 : ZMod p), 2, 3, 4]
  eq0 (x+y+z)
  eq0 [(1 : ZMod p),2,3].sum


#check Lean.Meta.transform
open Lean Meta in
@[inline]
partial def mytransformWithCache {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (cache : Std.HashMap ExprStructEq Expr)
    (pre   : Expr → m TransformStep := fun _ => return .continue)
    (post  : Expr → m TransformStep := fun e => return .done e)
    (usedLetOnly := false)
    (skipConstInApp := false)
    (skipInstances := false)
    : m (Expr × Std.HashMap ExprStructEq Expr) :=
  let _ : STWorld IO.RealWorld m := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) m := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr m Expr :=
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      let rec visitPost (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match (← post e) with
        | .done e      => pure e
        | .visit e     => visit e
        | .continue e? => pure (e?.getD e)
      let rec visitLambda (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | .lam n d b c =>
          withLocalDecl n c (← visit (d.instantiateRev fvars)) fun x =>
            visitLambda (fvars.push x) b
        | e => visitPost (← mkLambdaFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars)))
      let rec visitForall (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | .forallE n d b c =>
          withLocalDecl n c (← visit (d.instantiateRev fvars)) fun x =>
            visitForall (fvars.push x) b
        | e => visitPost (← mkForallFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars)))
      let rec visitLet (fvars : Array Expr) (e : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        match e with
        | .letE n t v b nondep =>
          withLetDecl n (← visit (t.instantiateRev fvars)) (← visit (v.instantiateRev fvars)) (nondep := nondep) fun x =>
            visitLet (fvars.push x) b
        | e => visitPost (← mkLetFVars (usedLetOnly := usedLetOnly) (generalizeNondepLet := false) fvars (← visit (e.instantiateRev fvars)))
      let visitApp (f : Expr) (arg : Expr) : MonadCacheT ExprStructEq Expr m Expr := do
        -- TODO we could use this
        -- if skipInstances then
        --   let infos := (← getFunInfoNArgs f args.size).paramInfo
        --   let mut args := args.toVector
        --   for h : i in *...args.size do
        --     let arg := args[i]
        --     if h : i < infos.size then
        --       let info := infos[i]
        --       if skipInstances && info.isInstance then
        --         continue
        --       args := args.set i (← visit arg)
        --     else
        --       args := args.set i (← visit arg)
        --   visitPost (mkAppN f args.toArray)
        -- else
          let f ← visit f
          let arg ← visit arg
          visitPost (mkApp f arg)
      match (← pre e) with
      | .done e  => pure e
      | .visit e => visit e
      | .continue e? =>
        let e := e?.getD e
        match e with
        | .forallE ..    => visitForall #[] e
        | .lam ..        => visitLambda #[] e
        | .letE ..       => visitLet #[] e
        | .app f arg     => visitApp f arg
        | .mdata _ b     => visitPost (e.updateMData! (← visit b))
        | .proj _ _ b    => visitPost (e.updateProj! (← visit b))
        | _              => visitPost e
  StateRefT'.run (visit input) cache

open Lean Meta in
def mytransform {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (input : Expr)
    (pre   : Expr → m TransformStep := fun _ => return .continue)
    (post  : Expr → m TransformStep := fun e => return .done e)
    (usedLetOnly := false)
    (skipConstInApp := false)
    : m Expr := do
  let (e, _) ← mytransformWithCache input {} pre post usedLetOnly skipConstInApp
  return e

open Lean Meta in
partial def unfoldSimplified' (name : Name) (args : Array Expr) (e : Expr) : Elab.Term.TermElabM Expr := do
  let toBeReduced := [`keyless, `poseidon, `mixS]
  let nArgs := [0, 1, 1]
  mytransform e
    (pre := fun e ↦ do
      let (name,args) := e.getAppFnArgs
      if name == .anonymous then return .continue
--      logInfo m!"{name} {args}"
      let isMatch := (toBeReduced.zip nArgs).any fun (toBeReducedName,nArgs) ↦
          (toBeReducedName = name && nArgs = args.size)

      if isMatch then
        logInfo m!"{e}"
        return .continue
      return .continue
    )

open Lean Meta in
partial def unfoldSimplified (toBeReduced : List (Name × Nat × Name)) (name : Name) (args : Array Expr) (e : Expr) : Elab.Term.TermElabM Expr := do
  -- logInfo m!"Simplifying[{name} {String.intercalate " " (←args.mapM (fun x ↦ (PrettyPrinter.ppExpr x) <&> Format.pretty)).toList}]:\n{e}"
  mytransform e
    -- (pre := fun e ↦ do
    --   if ←isTypeFormer e then return .done e
    --   if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e
    --   if e.isRawNatLit then return .continue
    --   logInfo m!"Pre: {e}"
    --   return .continue)
    (pre := fun e ↦ do

      if ←isTypeFormer e then return .done e
      if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e
      if e.isRawNatLit then return .continue

      match_expr ←inferType e with
      | Vector t n => -- check that t is ZMod p?
        let some n ← Lean.Meta.getNatValue? n | throwError ""
        let list ← (List.range n).mapM fun i ↦ mkAppM ``getElem! #[e, toExpr i]
        let array ← mkAppM ``Array.mk #[ ←mkListLit t list]
        let vecSansProof := mkAppN (.const ``Vector.mk [.zero]) #[t, toExpr n, array]

        let Expr.forallE _ t _ _ ← inferType vecSansProof | throwError "Expected function type."
        let vec := Expr.app vecSansProof (←mkEqRefl t)
        return .done vec
      | _ =>

      let (name,args) := e.getAppFnArgs
      if name == .anonymous then return .continue
--      logInfo m!"name: {name} args {args.size}"

      -- TODO this works but needs manual insight
      let some (_,_,simpSet) := toBeReduced.find? fun (toBeReducedName,nArgs,_) ↦
          (toBeReducedName = name && nArgs = args.size)
        | return .continue

      -- TODO not really working
      -- let funcT := ((←getEnv).find? name).get!.type
      -- -- Analyse the signature of `f`
      -- let vecLenIds ← forallTelescopeReducing funcT fun args _ ↦ do
      --   let mut res : FVarIdSet := {}
      --   for arg in args do
      --     let_expr Vector _ n := ←inferType arg | continue
      --     let fvars := collectFVars {} n |>.fvarSet
      --     res := res.union fvars
      --   --   logInfo m!"Collected fvars[{arg}]: {←fvars.toList.mapM (·.getUserName)}"
      --   -- logInfo m!"all fvars: {←res.toList.mapM (·.getUserName)}"
      --   return res
      -- -- Analyse the call site of `f`
      -- let isRightNumArgs := args.size = vecLenIds.size
      -- -- let isAllReduced ← args.allM fun e ↦ do
      -- --   let_expr Vector _ n := ←inferType e | return true
      -- --   let reducedN ← Meta.reduce n
      -- --   -- if n != reducedN then
      -- --   --   logInfo m!"Reduction did something.\n{n}→{reducedN}"
      -- --   -- logInfo m!"reduced: {reducedN} -- isRawNatLit: {reducedN.isRawNatLit}"
      -- --   return reducedN.isRawNatLit
      -- if !(isRightNumArgs) then return .continue

      -- TODO this matches too much stuff, r in mixS and v![1,2,3,4]
      -- if args.size = 0 then return .continue
      -- if !toBeReduced.contains name then return .continue
      -- let mut res : FVarIdSet := {}
      -- for arg in args do
      --   let fvars := collectFVars {} arg |>.fvarSet
      --   res := res.union fvars
      -- if !res.isEmpty then return .continue

      -- assuming vector lengths are the first arguments
      let funcBody := ((←getEnv).find? name).get!.value!
      -- logInfo m!"[{name}]funcbody: {funcBody}"
      let appliedVecLens := funcBody.instantiateLambdasOrApps args
      -- logInfo m!"[{name}]appliedVecLens: {appliedVecLens}"
      let simplified ← simplify simpSet appliedVecLens
      logInfo m!"[{name} {args}]simplified: {simplified}"
      return .visit simplified
      )

-- open Lean in
-- run_meta do
--   unjustTraverse `keyless #[.const `x [], .const `y []] ((←getEnv).find? `keyless).get!.value!

open Lean Meta Lean.Elab in
#eval show TermElabM _ from do
  let target := `keyless
  let toBeReduced := [(`keyless,0,`simpAll), (`poseidon,1,`simpAll), (`mixS,1,`simpAll)]
  let e := ((←getEnv).find? target).get!.value!
  let e ← unfoldSimplified toBeReduced target #[.const `x [], .const `y []] e
  let e ← simplify `simpAll e
  logInfo m!"{e}"
