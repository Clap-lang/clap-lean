import Lean
import Qq

import Clap.Compiler.BetaReduction
import Clap.Compiler.Collection
import Clap.Compiler.Trace

namespace Clap

open Lean Meta

namespace Compiler

namespace Simprocs

open Sym Simp Qq

section

instance {m} [Monad m] : AndThen (m Sym.Simp.Methods) where
  andThen a b := do return (←a) >> (←b ())

def simproc? (name : Name) : MetaM (Option ConstantInfo) := do
  let .some ci := (←getEnv).find? name | throwError m!"Undeclared constant: {name}"
  return if ci.type.isConstOf `Lean.Meta.Sym.Simp.Simproc
         then .some ci
         else .none

def isSimproc (name : Name) : MetaM Bool := return (←simproc? name).isSome

def getSimproc (name : Name) : MetaM Sym.Simp.Simproc := do
  discard (isSimproc name)
  let .ok sproc := unsafe (←getEnv).evalConst Sym.Simp.Simproc {} name
    | throwError m!"Failed to evaluate: {name}"
  return sproc

def orElse (names : Array Name) : MetaM Sym.Simp.Simproc := do
  let simprocs ← names.mapM getSimproc
  return simprocs.foldl (· <|> ·) (fun _ ↦ return .rfl)

def andThen (names : Array Name) : MetaM Sym.Simp.Simproc := do
  let simprocs ← names.mapM getSimproc
  return simprocs.foldl (· >> ·) (fun _ ↦ return .rfl)

/--
A simproc with logging enabled.
-/
def withLog (name : String) (f : Sym.Simp.Simproc) : Sym.Simp.Simproc :=
  fun e ↦ do
    let (res, time) ← Dbg.timeS (f e)
    match res with
      | .rfl .. =>
        recordSkippedRuleDbg name time
        return res
      | .step e' .. =>
        recordRuleDbg name time
        trace[Clap.Compile.dbg] m!"\n[{name}]\n{e}\n==>\n{e'}"
        return res

def simprocWithAtMostOnceGuard (proc: Sym.Simp.Simproc) : Sym.Simp.Simproc := fun expr ↦ do
  let dbgState ← getDbgState
  if dbgState.runUnfold then
    return .rfl
  else
    let res ← proc expr
    match res with
      | .rfl .. => return res
      | .step .. =>
        modifyDbgState (CompilerDbgState.setRunUnfold · true)
        return res

/--
A simproc of sequenced simprocs with logging enabled.

TODO(improve): We collapse certain rules like `Vector.range` and `List.range` with `lastComponent!`
-/
def andThenWithLog (names : Array Name) (atMostOnce: Bool := false) : MetaM Sym.Simp.Simproc := do
  let simprocs ← names.mapM getSimproc
  let guard := if atMostOnce then
    simprocWithAtMostOnceGuard
  else
    λ x => x
  return (simprocs.zip names).foldl (init := fun _ ↦ return .rfl) fun acc (proc, name) ↦
    acc >> guard (withLog name.lastComponent!.toString proc)

/--
A variation on `Lean.Meta.Sym.Simp.Theorems.rewrite` that composes with a logging proc.

TODO(improve): We collapse certain rules like `Vector.range` and `List.range` with `lastComponent!`
-/
def _root_.Lean.Meta.Sym.Simp.Theorems.rewriteWithLog
  (thms : Theorems) (d : Discharger := dischargeNone) : Sym.Simp.Simproc := fun e => do
  let mut anyCD := false
  for (thm, numExtra) in thms.getMatchWithExtra e do
    let rw := withLog thm.declName.get!.lastComponent!.toString (thm.rewrite (d := d))
    let result ←
      if numExtra == 0
      then rw e
      else simpOverApplied e numExtra rw
    anyCD := anyCD || result.isContextDependent
    if !result.isRfl then
      return if anyCD && !result.isContextDependent then result.withContextDependent else result
  return mkRflResultCD anyCD

def mkSimprocForWithLog
  (declNames : Array Name)
  (d : Discharger := dischargeNone)
  (atMostOnce : Bool := false)
: MetaM Sym.Simp.Simproc := do
  let mut thms : Theorems := {}
  for declName in declNames do
    thms := thms.insert (← mkTheoremFromDecl declName)
  if atMostOnce then
    return simprocWithAtMostOnceGuard (thms.rewriteWithLog d)
  else
  return thms.rewriteWithLog d

/--
Careful, `mkPostMethods` and `mkPreMethods` do not log.
-/
def mkPostMethods (declNames : Array Name)
                  (d : Discharger := Sym.Simp.dischargeNone) : MetaM Sym.Simp.Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← andThenWithLog procs.toArray

  let totalName := declNames.foldl (λ acc name => name.toString ++ acc) ""
  let proc := withLog totalName ((←mkSimprocFor thms.toArray d) >> procs)

  return { post := proc }

/--
I thought this would sigle-pass, but apparently not.
-/
def mkPostMethodsSinglePass (declNames : Array Name)
                            (d : Discharger := Sym.Simp.dischargeSimpSelf) : MetaM Sym.Simp.Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← orElse procs.toArray
  return { post := procs >> (←mkSimprocFor thms.toArray d) }

def mkPreMethods (declNames : Array Name)
                 (d : Discharger := Sym.Simp.dischargeNone) : MetaM Sym.Simp.Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let totalName := declNames.foldl (λ acc name => name.toString ++ acc) ""
  let procs ← andThen procs.toArray
  let proc := withLog totalName (procs >> (←mkSimprocFor thms.toArray d))
  return { pre := proc }

inductive PrePost where | Pre | Post
  deriving DecidableEq, Repr

instance : Inhabited PrePost := ⟨.Post⟩

def mkMethods (components : Array (Name × PrePost))
              (d : Discharger := Sym.Simp.dischargeNone)
              (atMostOnce : Bool := false)
              : MetaM Sym.Simp.Methods := do
  let (procs, thms) ← components.toList.partitionM fun (name, _) ↦ isSimproc name
  let (preProcs, postProcs) := partitionPrePost procs
  let (preThms, postThms) := partitionPrePost thms

  let preProcs ← andThenWithLog preProcs.toArray atMostOnce
  let preThms ← mkSimprocForWithLog preThms.toArray d atMostOnce
  let postProcs ← andThenWithLog postProcs.toArray atMostOnce
  let postThms ← mkSimprocForWithLog postThms.toArray d atMostOnce

  let pre := preProcs >> preThms
  let post := postProcs >> postThms
  return { pre := pre, post := post }

  where partitionPrePost (arg : List (Name × PrePost)) :=
    (arg.partition fun (_, prePost) ↦ prePost matches .Pre).map (·.map Prod.fst) (·.map Prod.fst)

end

section ExpressionAnalysis

def _root_.Lean.Expr.pure? (e : Expr) : Option Expr :=
  match_expr e with
  | Pure.pure _ _ _ x => .some x
  | Option.some   _ x => .some x
  | _                 => .none

def _root_.Lean.Expr.bind? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | Bind.bind _ _ _ _ a f => .some (a, f)
  | Option.bind   _ _ a f => .some (a, f)
  | _                     => .none

def _root_.Lean.Expr.bindInfo? (e : Expr) : Option (List Level × Array Expr) :=
  match_expr e with
  | Bind.bind _ _ α β a f => .some (e.getAppFn.constLevels!, #[α, β, a, f])
  | Option.bind   α β a f => .some (e.getAppFn.constLevels!, #[α, β, a, f])
  | _                     => .none

def _root_.Lean.Expr.range? (e : Expr) : Option Expr :=
  match_expr e with
  | List.range n   => .some n
  | Array.range n  => .some n
  | Vector.range n => .some n
  | _              => .none

def _root_.Lean.Expr.rangeInfo? (e : Expr) : Option (Expr × CollectionKind) :=
  match_expr e with
  | List.range n   => .some (n, .List)
  | Array.range n  => .some (n, .Array)
  | Vector.range n => .some (n, .Vector)
  | _              => .none

def _root_.Lean.Expr.foldlM? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.foldlM _ β α _ _ f init xs => .some [α, β, f, init, xs]
  | Array.foldlM α β _ _ f init xs _ _ => .some [α, β, f, init, xs]
  | List.foldlM _ _ β α f init xs => .some [α, β, f, init, xs]
  | _ => .none

def _root_.Lean.Expr.foldlMInfo? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.foldlM m β α _ inst f init xs => .some [m, inst, α, β, f, init, xs]
  | Array.foldlM α β m inst f init xs _ _ => .some [m, inst, α, β, f, init, xs]
  | List.foldlM m inst β α f init xs => .some [m, inst, α, β, f, init, xs]
  | _ => .none

def _root_.Lean.Expr.mapM? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.mapM _ α β _ _ f xs => .some [f, α, β, xs]
  | Array.mapM α β _ _ f xs    => .some [f, α, β, xs]
  | List.mapM _ _ α β f xs     => .some [f, α, β, xs]
  | _                          => .none

end ExpressionAnalysis

namespace Sets

namespace Structural

section MapM

open Compiler.Simp in
/--
Single step transformation. TODO: Does not play particularly nice with our top-level driver.
`Vector.mapM f #v[x₀, x₁, ..., xₘ]` ==>
`f x₀ >>= fun row₀ ↦ f x₁ >>= fun row₁ ↦ ... fun rowₘ ↦ .some #v[row₀, row₁, ..., rowₘ]`
-/
def _root_.Vector.mapM_mk : Sym.Simp.Simproc := fun e ↦ do
  let .some [f, _, β, xs] := e.mapM? | return .rfl
  let .some (elems, ⟨⟨_, k, .some sz⟩, _⟩) ← sequenced xs | return .rfl
  let szSimped := (←Sym.simpWithGround sz).getResultExpr sz
  if !Sym.isSameExpr sz szSimped then
    trace[Clap.Compile.simp.proc.vector_mapM_mk]
      m!"Info: Processing `Vector _ ({sz})` of ground length {szSimped}. Request:\n{e}"
  match szSimped.nat? with
  | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e} (TODO: Maybe this is ok.)"
  | .some szSimpedNat =>
    let transformedList ← Sym.mkListLit β <| (List.range szSimpedNat).reverse.map .bvar
    let .some transformedColl :=
      Collection.ofExpr transformedList <&>
      Collection.setSize (sz := szSimped) >>=
      Collection.cast (t := k) | unreachable!
    let transformedColl ← transformedColl.toExpr
    let transformedCollT ← Sym.inferType transformedColl
    let v ← Sym.getLevelInType transformedCollT
    let transformedColl? :=
      mkAppN (.const ``Option.some [v]) #[transformedCollT, transformedColl]
    let transformedColl? ← Sym.shareCommonInc transformedColl?
    let u ← Sym.getLevelInType β
    /-
    Start with `.some #[.bvar sz.pred, .bvar sz.pred.pred, ..., .bvar 0]`
    Prefix a single lambda in each iteration.
    -/
    let e' ← (List.range szSimpedNat).foldrM (init := transformedColl?) fun i e ↦ do
      let elem := elems[i]!
      liftM ∘ Sym.shareCommonInc <|
        mkAppN                                         -- `f vec[i] >>= fun row_{i} ↦ e`
          (.const ``Option.bind [u, v])
          #[
            β, transformedCollT,                       -- implicits
            ←Sym.shareCommonInc (f.beta #[elem]),      -- `f vec[i]`
            .lam (binderInfo := .default)
                 (binderName := .mkSimple s!"row_{i}")
                 (binderType := β)
                 (body       := e)                     -- `fun row_{i} ↦ e`
          ]
      -- Careful, `e` contains loose bvars until the very last iteration.
    trace[Clap.Compile.simp.proc.vector_mapM_mk]
      m!"\n{e}\n==>\n{e'}"
    let proof ← mkSorry (←mkEq e e') false
    -- Dbg.timeSince time "mapM_mk_cons took:"
    return .step e' proof

end MapM

section Control

def control : MetaM Sym.Simp.Methods := do
  mkMethods #[
    (`Lean.Meta.Sym.Simp.simpControl, .Pre)
  ]

end Control

section pureBindMany

/--
`pure a₁ >>= fun _ : τ₁ ↦ pure a₂ >>= fun _ : τ₂ ↦ ...` ==>
`[(a₁, τ₁, fun _ ↦ pure a₂ >>= fun _ ↦ ...), (a₂, τ₂, fun _ ↦ fun _ ↦ ...), ...]`
-/
partial def getBindPureLambdas (expr : Expr) : Option (List (Expr × Expr × Expr)) := do
  let (_, #[α, _, a, f]) ← expr.bindInfo? | .none
  let value ← a.pure?
  let .lam (body := body) .. := f | .none
  return (value, α, f) :: (getBindPureLambdas body).getD []

def substituteUnboundBvars (body : Expr) (values types : Array Expr) : Sym.SymM Expr := do
  let wrappedBody := types.foldr (init := body) fun argType acc => .lam `x argType acc .default
  return wrappedBody.beta values

/-
TODO this is currently extermely specialised and not correct in unhandled cases
needs to also substitute into actions
could do with perhaps calling the substitution function directly rather than beta reducing?
-/
def applyMany (body: Expr) (args: Array (Expr × Expr)) : Sym.SymM Expr := do
  let mut args := args
  for ((value, type), idx) in args.zipIdx do
    let (values, types) := args.unzip
    let value ← substituteUnboundBvars
      value
      (values.take idx)
      (types.take idx)
    let type ← substituteUnboundBvars
      type
      (values.take idx)
      (types.take idx)
    args := args.set! idx (value, type)
  let (values, types) := args.unzip
  substituteUnboundBvars body values types

/--
A single-pass handling of `pure_bind` chains.
In the spirit of `repeat rw [pure_bind]`.

`pure a₁ >>= fun x ↦ pure a₂ >>= fun y ↦ f x y` ==> `f a₁ a₂`
-/
def pureBindMany : Sym.Simp.Simproc := fun expr ↦ do
  match getBindPureLambdas expr with
  | .none => return .rfl
  | .some bindPurelambdas =>
    let .some (_, _, f) := bindPurelambdas.getLast? | return .rfl
    let .lam (body := body) .. := f | unreachable!
    let expr' ← applyMany body (
      bindPurelambdas.toArray.map fun (value, τ, _) => (value, τ)
    )
    return .step expr' (←mkSorry (←mkEq expr expr') false)

end pureBindMany

section flatten

open Lean Meta in
/--
TODO: Make tail rec.

A sequence of actions _in order_ as taken in a do block that is arbitrarily nested.
Variables bound by the intermediate lambdas are reindexed to preserve data flow,
i.e. interleaving the result with lambdas yields a semantically equivalent bind expression
that is strictly right-linear.
-/
partial def sequenceActions (e : Expr) : Sym.Simp.SimpM (Array Expr) := do
  trace[Clap.Compile.dbg]
    m!"Sequence Actions\n{e}"
  go e [0]
  where
  go (e : Expr) (Γ : List ℕ) : Sym.Simp.SimpM (Array Expr) := do
    trace[Clap.Compile.dbg]
      m!"Go\n{e}"
    match e.bind? with
    | .some (action, func) =>
      trace[Clap.Compile.dbg]
        m!"Outer Some"
      match action.bind? with
      | .some (b, g) =>
        trace[Clap.Compile.dbg]
          m!"Inner Some"
        -- b is a linearised sequence of actions, correctly rebound
        let b ← go b Γ
        -- g is a linearised sequence of actions, correctly rebound
        -- g is not correctly rebound in the Vector.set case of poseidon
        -- you can find this by searching for "[some (Vector.set #1 0 #0" and finding the one in the Inner Some summary when running the poseidon test in the test folder
        -- g in that case should either be [some (Vector.set #3 0 #0 ..)] or should be made as such here (I think it should just be returned as so)
        -- Additionally, the contents of Γ are never actually used, is it meant to be tracking how much bvars need to be adjusted?
        let g ← go g Γ
        let actions := b ++ g
        let lifted_func := (func.liftLooseBVars 0 actions.size.pred)
        let new_context := (actions.size :: Γ)
        /-
          `let x ← do a₁; a₂; a₃; ...; aₙ` offsets subsequent lambdas `n - 1` times.
          Note that `func` here is `λ x ↦ body`, so `x` is _bound_, i.e. not offset by
          `liftLooseBVars`.
        -/
        let actions' ← go lifted_func new_context
        let result_actions := actions ++ actions'
        trace[Clap.Compile.dbg]
          m!"Inner some\nb:{b}\ng:{g}\ncontext:{Γ}\nactions:{actions}\nlifted_func:{lifted_func}\nnew_context:{new_context}\nactions':{actions'}\nResult: \n{result_actions}"
        return result_actions
      | .none =>
        let processed_func ← go func Γ
        let result_actions := #[action] ++ processed_func
        trace[Clap.Compile.dbg]
          m!"Inner none\nfunc:{func}\nprocessed_func:{processed_func}\nResult: \n{result_actions}"
        return result_actions
    | .none =>
      trace[Clap.Compile.dbg]
        m!"Outer None"
      match e with
      | .lam (body := body) .. =>
        trace[Clap.Compile.dbg]
          m!"Lam"
        let result_actions ← go body Γ
        trace[Clap.Compile.dbg]
          m!"Lam\nbody:{body}\ncontext:{Γ}\nResult: \n{result_actions}"
        return result_actions
      | _ =>
        trace[Clap.Compile.dbg]
          m!"Non-lam"
        let result_actions := #[e]
        trace[Clap.Compile.dbg]
          m!"Non-lam\ne:{e}\ncontext:{Γ}\nResult: \n{result_actions}"
        return result_actions

/--
TODO(perf): This runs like a slow-running 🐕.
Blazing fast algorithm:
Left-to-right pass, count actions before each 🍃, bump that 🍃 by that many.
-/
partial def sequenceActions' (e : Expr) : Sym.Simp.SimpM (Array Expr) := do
  go e
  where
    go (e : Expr) : Sym.Simp.SimpM (Array Expr) := do
    match e.bind? with
    | .some (a₁, f₁) =>
      match a₁.bind? with
      | .some (a₂, f₂) =>
        let a₂ ← go a₂
        let f₂ := f₂.liftLooseBVars 0 a₂.size.pred
        let f₂ ← go f₂
        let a₂f₂ := a₂ ++ f₂
        let f₁ := f₁.liftLooseBVars 0 a₂f₂.size.pred
        let f₁ ← go f₁
        return a₂f₂ ++ f₁
      | .none =>
        --TODO: Oi dummy, do you even lift?
        -- `let f₁ := f₁.liftLooseBVars 0 ??`
        let f₁ ← go f₁
        return #[a₁] ++ f₁
    | .none =>
      match e with
      | .lam (body := body) .. => go body
      | _ =>
        return #[e]

-- def testFunc (a b c d e f: ℕ ) := a + b + c + d + e + f

-- def e : Expr := (Lean.Expr.lam
--         `d
--         (Lean.Expr.const `Nat [])
--         (Lean.Expr.lam
--           `e
--           (Lean.Expr.const `Nat [])
--           (Lean.Expr.lam
--             `f
--             (Lean.Expr.const `Nat [])
--             (Lean.Expr.app
--               (Lean.Expr.app
--                 (Lean.Expr.app
--                   (Lean.Expr.app
--                     (Lean.Expr.app
--                       (Lean.Expr.app
--                         (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
--                         (Lean.Expr.const `Nat []))
--                       (Lean.Expr.const `Nat []))
--                     (Lean.Expr.const `Nat []))
--                   (Lean.Expr.app
--                     (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
--                     (Lean.Expr.const `instAddNat [])))
--                 (Lean.Expr.app
--                   (Lean.Expr.app
--                     (Lean.Expr.app
--                       (Lean.Expr.app
--                         (Lean.Expr.app
--                           (Lean.Expr.app
--                             (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
--                             (Lean.Expr.const `Nat []))
--                           (Lean.Expr.const `Nat []))
--                         (Lean.Expr.const `Nat []))
--                       (Lean.Expr.app
--                         (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
--                         (Lean.Expr.const `instAddNat [])))
--                     (Lean.Expr.app
--                       (Lean.Expr.app
--                         (Lean.Expr.app
--                           (Lean.Expr.app
--                             (Lean.Expr.app
--                               (Lean.Expr.app
--                                 (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
--                                 (Lean.Expr.const `Nat []))
--                               (Lean.Expr.const `Nat []))
--                             (Lean.Expr.const `Nat []))
--                           (Lean.Expr.app
--                             (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
--                             (Lean.Expr.const `instAddNat [])))
--                         (Lean.Expr.app
--                           (Lean.Expr.app
--                             (Lean.Expr.app
--                               (Lean.Expr.app
--                                 (Lean.Expr.app
--                                   (Lean.Expr.app
--                                     (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
--                                     (Lean.Expr.const `Nat []))
--                                   (Lean.Expr.const `Nat []))
--                                 (Lean.Expr.const `Nat []))
--                               (Lean.Expr.app
--                                 (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
--                                 (Lean.Expr.const `instAddNat [])))
--                             (Lean.Expr.app
--                               (Lean.Expr.app
--                                 (Lean.Expr.app
--                                   (Lean.Expr.app
--                                     (Lean.Expr.app
--                                       (Lean.Expr.app
--                                         (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
--                                         (Lean.Expr.const `Nat []))
--                                       (Lean.Expr.const `Nat []))
--                                     (Lean.Expr.const `Nat []))
--                                   (Lean.Expr.app
--                                     (Lean.Expr.app
--                                       (Lean.Expr.const `instHAdd [Lean.Level.zero])
--                                       (Lean.Expr.const `Nat []))
--                                     (Lean.Expr.const `instAddNat [])))
--                                 (Lean.Expr.bvar 5))
--                               (Lean.Expr.bvar 4)))
--                           (Lean.Expr.bvar 3)))
--                       (Lean.Expr.bvar 2)))
--                   (Lean.Expr.bvar 1)))
--               (Lean.Expr.bvar 0))
--             (Lean.BinderInfo.default))
--           (Lean.BinderInfo.default))
--         (Lean.BinderInfo.default))

/--
Optimises `bindActionsInferType`.
TODO(untested)
TODO(unused)
TODO(perf) Should also grab universes...
-/
def _bindActions (a₁ a₁type a₂ a₂type: Expr) : Sym.Simp.SimpM (Expr × Expr) := do
  let cont := Expr.lam `a a₁type a₂ default
  let bind :=
    mkApp4 (.const ``Option.bind [←Sym.getLevelInType a₁type, ←Sym.getLevelInType a₂type])
           a₁type a₂type
           a₁
           cont
  return (bind, a₂type)

/--
Optimises `chainActionsInferType`.
TODO(untested)
TODO(unused)
TODO(perf) Should also grab universes...
-/
def _chainActions (t : Expr) (actions : Array (Expr × Expr)) : Sym.Simp.SimpM Expr := do
  let .some (action, _) := actions.back? | throwError m!"expected some action"
  let actions := actions.pop
  let (e', _) ← actions.foldrM (init := (action, t)) fun (a₁, ta₁) (a₂, ta₂) ↦
    _bindActions a₁ ta₁ a₂ ta₂
  let e' ← Sym.shareCommonInc e'
  return e'

/--
A `bind a₁ λ x ↦ a₂ x` given `a₁` and `a₂`.

TODO(perf): Can cache types during traversal.
-/
def bindActionsInferType (action actionτ f fτ : Expr) : Sym.Simp.SimpM (Expr × Expr) := do
  -- trace[Clap.Compile.dbg]
  --   m!"BindActionsInferType\naction\n{action}\nActionType\n{actionτ}\nf\n{f}\nfτ\n{fτ}"
  let cont := Expr.lam `a actionτ f .default
  -- trace[Clap.Compile.dbg]
  --   m!"cont\n{cont}"
  let bind :=
    mkApp4 (.const ``Option.bind [←Sym.getLevelInType actionτ, ←Sym.getLevelInType fτ])
           actionτ fτ
           action
           cont
  trace[Clap.Compile.dbg]
    m!"bind\n{bind}"
  return (bind, fτ)

/--
A sequence of expressions from `actions` intercalated with single-argument lambdas.

TODO(perf): Can cache types during traversal.
-/
def chainActionsInferType (actions : Array Expr) : Sym.Simp.SimpM Expr := do
  let actions ← actions.mapM fun action ↦ do
    let_expr Option τ := ←Sym.inferType action | throwError m!"expected option"
    return (action, τ)
  let .some action := actions.back? | throwError m!"expected some action"
  let actions := actions.pop
  let (e', _) ← actions.foldrM (init := action) fun (elemAction, elemType) (accAction, accType) ↦
    bindActionsInferType elemAction elemType accAction accType
  let e' ← Sym.shareCommonInc e'
  return e'

/--
A flat sequence of actions from an expression that nests `bind`s arbitrarily.
The result is thus a strict right-leaning linear tree of the form
`a₀ >>= λ x₁ ↦ a₁ >>= λ x₂ ↦ ...`.

E.g.
`do a₀`
`   let x ← do a₁; a₂`
`   a₃ x`
==>
`do a₀`
`   a₁`
`   let x ← a₂`
`   a₃ x`
-/
def flattenBindsAny : Sym.Simp.Simproc := fun e ↦ do
  let .some (a, _) := e.bind? | return .rfl
  let .some (_, _) := a.bind? | return .rfl
  let e' ← sequenceActions' e
  let e' ← chainActionsInferType e'
  return .step e' (←mkSorry (←mkEq e e') false)

end flatten

section FoldlM

/--
`[1, 2, 3, 4].foldlM f b` ==>
`f b 1 >>= λ next → f next 2 >>= λ next → f next 3 >>= λ next ↦ pure next`
-/
def foldlM : Sym.Simp.Simproc := fun expr ↦ do
  let .some [inputType, outputType, f, init, collection] := expr.foldlM? | return .rfl
  let .some (elems, ⟨⟨_, _, .some size⟩, _⟩) ← sequenced collection | return .rfl

  let u ← Sym.getLevelInType outputType
  let v ← Sym.getLevelInType inputType

  let szSimped := (←Sym.simpWithGround size).getResultExpr size
  match szSimped.nat? with
  | .none => throwError m!"{size} does not simplify to ground. Expr:\n{expr} (TODO: Maybe this is ok.)"
  | .some 0 =>
    -- For an empty collection, return `some init`
    let expr' ← Sym.shareCommonInc <| mkAppN (.const ``Option.some [u]) #[outputType, init]
    return .step expr' (←mkSorry (←mkEq expr expr') false)
  | .some _szSimpedNat =>
    -- `some next`
    let chain_base ← Sym.shareCommonInc <| mkAppN (.const ``Option.some [u]) #[outputType, .bvar 0]

    -- repeated `(f x elem).bind fun x => acc`
    let chain := elems.foldr (
      λ (elem: Expr) (acc: Expr) =>
        let bind_lhs := mkApp2 f (.bvar 0) elem
        let bind_rhs := Expr.lam `next outputType acc .default
        let bind := mkApp4 (.const `Option.bind [v, u]) outputType outputType bind_lhs bind_rhs
        bind
    ) chain_base

    let wrapped_chain := Expr.lam `init outputType chain .default
    let reduced_chain := wrapped_chain.beta #[init]
    let expr' ← Sym.shareCommonInc <| reduced_chain

    trace[Clap.Compile.dbg]
      m!"\n{expr}\n==>\n{expr'}"

    return .step expr' (←mkSorry (←mkEq expr expr') false)

/--
`#v[a₁, a₂, ...].foldlM (init := x) f`
`f a₁ x >>= fun rest ↦ [a₂, ...].foldlM (init := rest) f`
-/
def foldlM_stagger : Sym.Simp.Simproc := fun e ↦ do
  let .some [m, inst, α, β, f, init, collection] := e.foldlMInfo? | return .rfl
  -- TODO(perf): `coll` not necessary in full
  let .some ⟨_, listExpr⟩ := Collection.ofExpr collection | return .rfl
  let u₁ ← Sym.getLevelInType β
  let u₂ := u₁
  let u₃ ← Sym.getLevelInType α
  match_expr listExpr with
  | List.cons _ hd tl =>
    let head ← Sym.shareCommonInc <| f.beta #[init, hd]
    let tail ← Sym.shareCommonInc <| mkApp7 (.const ``List.foldlM [u₁, u₂, u₃])
                                            m inst
                                            β α f (.bvar 0) tl
    let lambda ← Sym.shareCommonInc <| .lam `next β tail .default
    let tailτ ← Sym.inferType tail
    let tailτu ← Sym.getLevelInType tailτ
    let e' ← Sym.shareCommonInc <| mkApp4 (.const ``Option.bind [u₁, tailτu]) β tailτ head lambda
    -- let e' ← Sym.shareCommonInc <| Simp.wrapped (←Sym.inferType e') e'
    -- logWarning m!"HELLO!"
    return .step e' (←mkSorry (←mkEq e e') false) (done := true)
  | _ =>
    let e' := mkApp2 (.const ``Option.some [u₁]) β init
    return .step e' (←mkSorry (←mkEq e e') false) (done := true)

end FoldlM

section Explode

def dontExplodeVector : Sym.Simp.Simproc := fun e ↦ do
  let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | return .rfl
  unless coll.isFVar && (←Sym.inferType coll).isAppOf ``Vector do return .rfl
  trace[Clap.Compile.simp.proc.kaboom] m!"Marked done:\n{e}"
  return .rfl (done := true)

/--
TODO: The proof is not `rfl`. One can prove all of these `by aesop (add cases [Vector, Array, List])`,
      but I'd rather not lift to `aesop` and build the proof by hand (viz. `abc'` above).
-/
def explodeVector (who : String := "") : Sym.Simp.Simproc := fun e ↦ do
  let t ← Sym.inferType e
  let_expr Vector t sz := t | return .rfl
  unless e.isFVar do return .rfl
  let sz' ← Sym.simpWithGround sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground.\nExpr:\n{e}"
  | .some _n => let explodedVec ← (sequenceAsVecExpr e t (sz'.getResultExpr sz)).run'
                trace[Clap.Compile.simp.proc.kaboom] m!"{who}"
                -- trace[Clap.Compile.simp.proc.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
                return .step explodedVec (←mkSorry (←mkEq e explodedVec) false)


def explode : MetaM Sym.Simp.Methods := do
  return {
    pre  := dontExplodeVector >> explodeVector
  }

end Explode

section Ground

def evalGround : Sym.Simp.Simproc := fun e ↦ do
  match ←Sym.Simp.evalGround {} e with
  | res@(.rfl ..) => return res -- trace[Clap.Compile.simp.proc.evalGround] m!"skipped: {e}"; return res
  | res@(.step ..) => return res -- trace[Clap.Compile.simp.proc.evalGround] m!"ground hit: {e}"; return res

end Ground

def logVisit (tag: String) : Sym.Simp.Simproc := fun expr ↦ do
  let_expr HAdd.hAdd _ _ _ _ _ _ := expr | return .rfl
  let_expr HAdd.hAdd _ _ _ _ x y := expr | return .rfl
  let x := Sym.getNatValue? x
  let y := Sym.getNatValue? y
  match x, y with
    | .some 1, some 2 =>
      let res ← evalGround expr
      logInfo m!"Grounded: {res.getResultExpr expr} {tag}"
      return .rfl
    | _, _ =>
      logInfo m!"LoggedVisit: {expr} {tag}"
      return .rfl

def logVisitStructural := logVisit "structural"
def logVisitFunctional := logVisit "functional"
def logVisitGeneral := logVisit "general"

def structural : MetaM Sym.Simp.Methods :=
  -- mkMethods #[(`Clap.Compiler.Sets.Structural.logVisitStructural, .Pre)] >>
  mkMethods #[
    (``Sets.Structural.pureBindMany, .Pre),
    (``Sets.Structural.flattenBindsAny, .Pre),
    (``Sets.Structural.foldlM, .Pre),
    (``Vector.mapM_mk, .Pre)
  ]

end Structural

namespace General

section Control

def control : MetaM Sym.Simp.Methods := do
  mkMethods #[(`Lean.Meta.Sym.Simp.simpControl, .Pre)]

end Control

section GetElem

def getElem : Sym.Simp.Simproc := fun e ↦ do
  /-
  TODO(perf):
  In vector, we can optimise by not enumerating all elements first,
  and then taking the size of the final list.

  Instead, we can simply traverse the first `i` conses, as we have the length apriori for the proof.
  Or some such.
  -/
  let_expr GetElem.getElem _ _ _ _ _ vec n _ := e | return .rfl
  let .some (elems, t) := Collection.elemsOfExpr vec | return .rfl
  let .some sz := t.type.sz | unreachable!
  let n := (←Sym.simpWithGround n).getResultExpr n
  let .some i := Sym.getNatValue? n | return .rfl
  if h : i < elems.size
  then
    let e' := elems[i]
    return .step e' (←Sym.mkEqRefl e')
  else
    return .rfl

end GetElem

section Append

def append : Sym.Simp.Simproc := fun e ↦ do
  let_expr HAppend.hAppend _ _ _ _ xs ys := e | return .rfl

  let .some ⟨xsElems, xsC⟩ ← sequenced xs | return .rfl
  let .some ⟨ysElems, ysC⟩ ← sequenced ys | return .rfl

  let append := xsElems.append ysElems

  -- `xs.type.t = ys.type.t` ∧ `xs.type.k = ys.type.k`
  let .some appendListColl := Collection.ofExpr (←Sym.mkListLit xsC.type.t append.toList) | unreachable!
  let instAdd := Expr.const ``instAddNat []
  let inst ← Sym.shareCommonInc <| mkApp2 (.const ``instHAdd [0]) q(ℕ) instAdd
  let .some szXs := xsC.type.sz | unreachable!
  let .some szYs := ysC.type.sz | unreachable!
  let sz := mkApp6 (.const ``HAdd.hAdd [0, 0, 0]) q(ℕ) q(ℕ) q(ℕ) inst szXs szYs
  let .some appendVecColl := appendListColl.setSize sz |>.cast xsC.type.k | unreachable!
  let e' ← appendVecColl.toExpr

  return .step e' (←mkSorry (←mkEq e e') false)

end Append

section Range

def range : Sym.Simp.Simproc := fun e ↦ do
  let .some (n, kind) := e.rangeInfo? | return .rfl
  let nSimped ← Sym.simpWithGround! n
  match Sym.getNatValue? nSimped with
  | .none =>
    logError m!"Cannot produce range without being able to evaluate:\n{nSimped}"
    return .rfl
  | .some n =>
    let l := _root_.List.range n
    let .some collection := Collection.ofExpr (Lean.toExpr l) | unreachable!
    let .some collection := collection.setSize (mkNatLit n) |>.cast kind | unreachable!
    let e' ← collection.toExpr
    return .step e' (←Sym.mkEqRefl e')

end Range

section Size

def size : MetaM Sym.Simp.Methods :=
  mkMethods #[
    (``Vector.size_toArray, .Post),
    (``List.size_toArray, .Post),
    (``List.length_cons, .Post),
    (``List.length_nil, .Post)
  ]

end Size

section Foldr

/--
Gets around `Array.foldr` partial application-ness.
-/
def foldr_toArray : Sym.Simp.Simproc := fun e => do
  let_expr Array.foldr α β f init xs _ _ := e | return .rfl
  let .some ⟨_, xs⟩ := Collection.ofExpr xs | throwError m!"cannot foldr:\n{xs} in:\n{e}"
  let e' ← Sym.shareCommonInc <| mkApp5 (.const ``List.foldr e.getAppFn.constLevels!) α β f init xs
  return .step e' (←mkSorry (←mkEq e e') false)

def foldr : MetaM Sym.Simp.Methods :=
  mkMethods #[
    (``Vector.foldr_mk, .Post),
    (``foldr_toArray, .Post),
    (``List.foldr_cons, .Post),
    (``List.foldr_nil, .Post)
  ]

end Foldr

section Sum

def sum : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Vector.sum_eq_foldr
  ]

end Sum

section Set

/--
TODO: Generalise to lists and arrays.
-/
def set : Sym.Simp.Simproc := fun e => do
  let_expr _root_.Vector.set t sz xs i x _ := e | return .rfl
  let some (xs, _, _) := vectorElemsOfMk xs | return .rfl
  let iGround := (←Sym.simpWithGround i).getResultExpr i
  match Sym.getNatValue? iGround with
  | .none => throwError m!"Not ground: {iGround}. Request:\n{e}"
  | .some iNat =>
    -- TODO: I guess we can `Vector.set` with `h`.
    let result ← Sym.mkListLit t (xs.set! iNat x).toList
    let e' ← mkVecLit t result sz

    return .step e' (←mkSorry (←mkEq e e') false)

end Set

section MapIdx

def mapIdx : Sym.Simp.Simproc := fun e => do
  let_expr Vector.mapIdx _ outputType sz f xs := e | return .rfl
  let some (xs, _) := vectorElemsOfMk xs | return .rfl

  let result ← Sym.mkListLit outputType (xs.mapIdx (f.beta #[mkNatLit ·, ·])).toList
  let e' ← mkVecLit outputType result sz

  return .step e' (←mkSorry (←mkEq e e') false)

end MapIdx

def general : MetaM Sym.Simp.Methods :=
  -- mkMethods #[(`Clap.Compiler.Sets.Structural.logVisitGeneral, .Pre)] >>
  control >>
  mkMethods #[
    (``Sets.General.getElem, .Post),
    (``Sets.General.append, .Post),
    (`Clap.Compiler.Sets.Structural.evalGround, .Post),
    (``Sets.General.set, .Post),
    (``Sets.General.mapIdx, .Post)
  ]
  >>
  size
  >>
  sum
  >>
  Clap.Compiler.Simprocs.Sets.General.foldr
  >>
  mkMethods #[
    (``Sets.General.range, .Post)
  ]

end General

namespace Functional

section Zeta

/--
This is more or less `Lean.Meta.Tactic.Cbv.zetaReduce`, which seems to not be exported.

In `Sym`, maybe we can choose to not `zeta` certain things without breaking `simp`?
-/
def zetaReduce : Sym.Simp.Simproc := fun e ↦ do
  let .letE _ _ value body _ := e | return .rfl
  let e' ← Sym.share (expandLet body #[value])
  -- trace[Clap.Compile.simp.proc.zeta]
  --   m!"\n{e}\n==>\n{new}"
  return .step e' (←Sym.mkEqRefl e')

end Zeta

def functional : MetaM Sym.Simp.Methods :=
  -- mkMethods #[(`Clap.Compiler.Sets.Structural.logVisitFunctional, .Pre)] >>
  mkMethods #[
    (``Clap.Compiler.Sets.Functional.betaReduce, .Pre),
    (``Sets.Functional.zetaReduce, .Pre)
  ]

end Functional

end Sets

end Simprocs

end Compiler

end Clap
