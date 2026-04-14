import Clap.Spec
import Clap.Compiler.Reduce
import Clap.Compiler.Basic
import Qq

open Clap Spec Compiler Qq

namespace Dummy

-- set_option debug.skipKernelTC true
-- set_option maxRecDepth 1000000
-- set_option maxHeartbeats 800000
-- set_option trace.Clap.Compiler true
-- set_option trace.Clap.Compiler.preprocess true
-- set_option profiler true
-- set_option profiler.threshold 0

abbrev p := Primes.bn254

def mixS (n : ℕ) (r:ℕ) (x : Vector (ZMod p) n) : Option (Vector (ZMod p) n) := do
  eq0 (x[0]! + (x.sum : ZMod p) + (r : ZMod p))
  x.mapM (return ·+1)

def poseidon (n:ℕ) (x : Vector (ZMod p) n) : Option (ZMod p) := do
  let state ← (List.range 4).foldlM (fun state r ↦ mixS (n := n) r state) (init:=x)
  state.sum

def keyless (x : Vector (ZMod p) 2) (y : Vector (ZMod p) 4) : Option Unit := do
  let x ← poseidon _ x
  let y ← poseidon _ y
  let z ← poseidon _ #v[(1 : ZMod p), 2, 3, 4]
  eq0 (x+y+z)
  eq0 [(1 : ZMod p),2,3].sum


--#check Lean.Meta.transform
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

--example : Vector ℕ 2 := Vector.mk #[0,1] (by apply List.size_toArray)

open Lean Meta Elab

-- array.size = 2
-- @Eq.refl _ _

example : Vector.mk #[1, 2] (show #[1, 2].size = 2 from Eq.refl #[1, 2].size) = sorry := sorry


def sequenceAsVecExpr (name : Expr) (t : Expr) (len : ℕ) : MetaM Expr := do
  let array ← mkAppM ``Array.mk #[
    ←mkListLit t (←List.range len |>.mapM fun i ↦ do mkAppM ``GetElem?.getElem! #[
      name,
      Expr.lit (.natVal i)
    ])
  ]
  let vecSansProof := mkAppN (.const ``Vector.mk [.zero]) #[t, toExpr len, array]
  return Expr.app vecSansProof (←mkAppM ``Eq.refl #[←mkAppM ``Array.size #[array]])

-- def vec : Vector Nat 2 → Vector Nat 2 := fun v ↦ v

-- run_meta
--   let x := (←getEnv).find? `vec |>.get!
--   let xval := x.value!
--   lambdaTelescope xval fun args _ ↦ do
--     let #[arg] := args | throwError m!"Impossible."
--     logWarning m!"{←sequenceAsVec (←arg.fvarId!.getUserName) q(Nat) 2}"

def collectionTypeAndSize (e : Expr) : TermElabM (Expr × Expr) := do
  let_expr Vector t n := ←inferType e | throwError m!"Not a collection:\n{e}"
  return (t, ←simplify `simpAll n)

def needsExploding (e : Expr) : TermElabM Bool := do
  let t ← inferType e
  return t.isAppOf ``Vector

def explodeSequences (e : Expr) : TermElabM Expr := do
  Meta.transform (skipConstInApp := true) e fun e ↦ do
    if e.isFVar && (←needsExploding e)
    then logInfo m!"Exploding: {e}"
         let (t, sz) ← collectionTypeAndSize e
         logInfo m!"t: {t} sz: {sz}"
         return .done <| ←sequenceAsVec (←e.fvarId!.getUserName)
                                        t
                                        sz.nat?.get!
    else return .continue

def explodeSequencesBvar (e : Expr) : TermElabM Expr := do
  Meta.transform (skipConstInApp := true) e fun e ↦ do
    if e.isBVar && (←needsExploding e)
    then logInfo m!"Exploding: {e}"
         let (t, sz) ← collectionTypeAndSize e
         logInfo m!"t: {t} sz: {sz}"
         return .done <| ←sequenceAsVecExpr e t sz.nat?.get!
    else return .continue

open Lean Meta Clap Compiler in
partial def lambdaWithExpandedVecs (e : Expr) : TermElabM Expr :=
  lambdaTelescope e fun args body ↦ do
    let body ← explodeSequences body
    mkLambdaFVars args body

def vec : Vector Nat 2 := #v[1, 2]

open Lean Meta Lean.Elab in
#eval show TermElabM _ from do
  let name := ``keyless
  let e := ((←getEnv).find? name).get!.value!
  let e ← lambdaWithExpandedVecs e
  logInfo m!"{e}"

open Lean Meta in
partial def unfoldSimplified (toBeReduced : List (Name × Nat × Name)) (e : Expr) : Elab.Term.TermElabM Expr := do
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
      if Lean.isClass (←getEnv) (←inferType e).getAppFnArgs.1 then return .done e -- TODO can be done with skipInstances?
      if e.isRawNatLit then return .continue
      let (name,args) := e.getAppFnArgs
      if name == .anonymous then return .continue
      -- logInfo m!"name: {name} args {args.size}"
      -- TODO this works but needs manual insight
      let some (_,_,simpSet) := toBeReduced.find? fun (toBeReducedName,nArgs,_) ↦
          (toBeReducedName = name && nArgs = args.size)
        | return .continue
      -- logInfo m!"found candidate{name} args: {args}"
      -- assuming vector lengths are the first arguments
      let funcBody := ((←getEnv).find? name).get!.value!
      -- logInfo m!"[{name}]funcbody: {funcBody}"
      let appliedVecLens := funcBody.instantiateLambdasOrApps args
      let appliedVecLens ← explodeSequences appliedVecLens
      -- let appliedVecLens ← lambdaWithExpandedVecs appliedVecLens -- TODO: Maybe do this in intermediate lambdas as well. (MUY IMPORTANTE)
      -- logInfo m!"[{name}]appliedVecLens: {appliedVecLens}"
      logInfo m!"[{name} {args}]simplifying: {appliedVecLens}"
      let simplified ← simplify simpSet appliedVecLens
      let simplified ← explodeSequences simplified
      let simplified ← simplify simpSet simplified
      logInfo m!"[{name} {args}]simplified: {simplified}"
      return .visit simplified
      )
#check Meta.transform
#check Core.transform
-- open Lean in
-- run_meta do
--   unjustTraverse `keyless #[.const `x [], .const `y []] ((←getEnv).find? `keyless).get!.value!

-- elab "abc" : tactic =>
--   return ()

-- open Lean Tactic Elab in
-- lemma machiavelli : True := by
--   let machiavelli : TacticM Unit := do
--     discard <| IO.Process.run {
--       cmd := "echo",
--       args := #["Launching missiles. Stealing your wallet. Stealing your girlfriend."]
--     }
--     IO.println "You've been pwn'd.\n[x] rekt [ ] not rekt"
--   run_tac machiavelli
--   exact True.intro

-- #synth NeZero Primes.bn254
attribute [-simp] explodeVectorProc
open Lean Meta Lean.Elab in
#eval show TermElabM _ from do
  let target := ``keyless
  -- logWarning m!"{repr ((←getEnv).find? target).get!.value!}"
  let toBeReduced := [(target,0,`simpAll), (``Dummy.poseidon,1,`simpAll), (``Dummy.mixS,1,`simpAll)]
  let e ← unfoldSimplified toBeReduced (.const target [])
  let e ← simplify `simpAll e
  logInfo m!"{e}"

end Dummy
