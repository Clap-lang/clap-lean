import Lean
import Qq

import Lean.Meta.Sym.SymM
import Lean.Meta.Tactic.Cbv.Main

import Clap.Lang
import Clap.Spec
import Clap.Compiler.BetaReduction
import Clap.Compiler.Collection
import Clap.Compiler.Trace
import Clap.Compiler.Simp
import Clap.Compiler.Vectors
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean Meta Qq Elab

instance {m} [Monad m] : AndThen (m Sym.Simp.Methods) where
  andThen a b := do return (←a) >> (←b ())

@[inherit_doc Simp.wrapped]
abbrev singlePass := Simp.wrapped

section

open Sym.Simp Sym

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
def withLog (name : String) (f : Simproc) : Simproc :=
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

def simprocWithAtMostOnceGuard (proc: Simproc) : Simproc := fun expr ↦ do
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
  (thms : Theorems) (d : Discharger := dischargeNone) : Simproc := fun e => do
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
: MetaM Simproc := do
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
                  (d : Discharger := Sym.Simp.dischargeNone) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← andThenWithLog procs.toArray

  let totalName := declNames.foldl (λ acc name => name.toString ++ acc) ""
  let proc := withLog totalName ((←mkSimprocFor thms.toArray d) >> procs)

  return { post := proc }

/--
I thought this would sigle-pass, but apparently not.
-/
def mkPostMethodsSinglePass (declNames : Array Name)
                            (d : Discharger := Sym.Simp.dischargeSimpSelf) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← orElse procs.toArray
  return { post := procs >> (←mkSimprocFor thms.toArray d) }

def mkPreMethods (declNames : Array Name)
                 (d : Discharger := Sym.Simp.dischargeNone) : MetaM Methods := do
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
              : MetaM Methods := do
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

namespace Monad

def monad : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc, ``bind_assoc,
    ``Option.pure_def,
    ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
    ``Option.map_eq_map, ``Option.map_some
  ]

end Monad

namespace General

-- /--
-- This is more or less `Lean.Meta.Tactic.Cbv.zetaReduce`, which seems to not be exported.

-- In `Sym`, maybe we can choose to not `zeta` certain things without breaking `simp`?
-- -/
-- def zetaReduce : Simproc := fun e ↦ do
--   let .letE _ _ value body _ := e | return .rfl
--   let new := expandLet body #[value]
--   let new ← Sym.share new
--   -- trace[Clap.Compile.simp.proc.zeta]
--   --   m!"\n{e}\n==>\n{new}"
--   return .step new (←Sym.mkEqRefl new)

def getApplicationChain (e: Expr) (depth: ℕ): Option (Expr × List Expr) := do
  if depth = 0 then .none
  let .app function arg := e | .none
  let .some (inner_function, args) := getApplicationChain function (depth - 1) | .some (function, [arg])
  return (inner_function, arg::args)

-- /--
-- This is more or less `Lean.Meta.Tactic.Cbv.betaReduce`, which seems to not be exported.
-- -/
-- def betaReduce : Simproc := fun e ↦ do
--   let (function@(.lam ..), args@⟨(.cons _ _)⟩) := e.withApp (·, ·) | return .rfl
--   let e' ← Sym.shareCommonInc <| function.beta args
--   return .step e' (←Sym.mkEqRefl e')

  -- let Expr.app function arg := e | return .rfl
  -- let (Expr.lam _ _ _ _) := function | return .rfl
  -- let .some (function, args) := getApplicationChain e 2 | return .rfl
  -- Dbg.timeSince timeα "getApp[2]"

  -- let timeα ← IO.monoMsNow
  -- let .some (function, args) := getApplicationChain e 1 | return .rfl
  -- Dbg.timeSince timeα "getApp[1]"

  -- logWarning m!"function: {function}\nargs: {args}\nfunction: {function'}\nargs': {args'}"
  -- let .lam _ _ _ _ := function | return .rfl
  -- let args := args.toArray
  -- let e' ← Sym.shareCommonInc <| function.betaRev args

  -- trace[Clap.Compile.simp.proc.beta]
  --   m!"\n{e}\n==>\n{e'}\nharr:{args.size}"
  -- return .step e' (←Sym.mkEqRefl e')

-- def zeta : MetaM Methods := do
--   return {
--     pre := zetaReduce
--   }
#check Sets.Functional.betaReduce
def beta : MetaM Methods := do
  mkPreMethods #[
    `Clap.Compiler.SymSets.General.betaReduce
  ]
  >>
  mkPostMethods #[
    `Clap.Compiler.SymSets.General.betaReduce
  ]

-- TODO work out how to unmark things done
-- So that if an if's condition takes multiple iterations to reduce
-- we are able to still process the if
def control : MetaM Methods := do
  return {
    pre := simpControl
  }

def compilerSet_bind_eq_bind : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_eq_bind
  ]

def compilerSet_bind_assoc : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc, ``bind_assoc
  ]

def compilerSet_bind_pure : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_some, ``bind_pure, ``pure_bind
  ]

def compilerSet_bind_some : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_some
  ]

def compilerSet_whatever : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc, ``bind_assoc,
    ``Option.pure_def,
    ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
    ``Option.map_eq_map, ``Option.map_some, ``Option.pure_apply
  ]

def optionPureApply : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.pure_apply
  ]

def compilerSet_old : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc, ``bind_assoc,
    ``Option.pure_def,
    ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
    ``Option.map_eq_map, ``Option.map_some, ``Option.pure_apply
  ]

def compilerSet_old' : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc,
    ``Option.pure_def,
    ``Option.bind_fun_some,
    ``Option.bind_some,
    ``Option.map_eq_map,
    ``Option.map_some,
    ``Option.bind_eq_bind,
    ``Option.pure_apply
  ]

def compilerSet : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.pure_def, ``Option.bind_some, ``Option.bind_eq_bind
  ]

-- `fun x ↦ (x, fun x ↦ x)`

/--
TODO: Account for `PUnit` and such.
-/
def isOptionUnit (e : Expr) : Bool := Id.run do
  let_expr Option x := e | return false
  return x.isConstOf ``Unit

-- vec ==> #v[vec[0], vec[1]][0] : GetElem (1 + 1)
-- Vector.mk 2 ... |>.getElem (1 + 1)

def monad : Sym.Simp.Simproc := fun e ↦ do
  match_expr e with
  | Bind.bind _ _ α β x f =>
    let u ← Sym.getLevelInType α
    let v ← Sym.getLevelInType β
    let e' ← shareCommonInc <| mkApp4 (.const ``Option.bind [u, v]) α β x f
    trace[Clap.Compile.simp.proc.monad.bind_eq_bind]
      m!"\n{e}\n==>\n{e'}"
    return .step e' (←Sym.mkEqRefl e')
  | Pure.pure _ _ α x =>
    let u ← Sym.getLevelInType α
    let e' ← shareCommonInc <| mkApp2 (.const ``Option.some [u]) α x
    trace[Clap.Compile.simp.proc.monad.pure_apply]
      m!"\n{e}\n==>\n{e'}"
    return .step e' (←Sym.mkEqRefl e')
  | Option.bind α γ x g =>
    match_expr x with
    -- | Option.bind α β x f =>
    --   -- let time ← IO.monoMsNow
    --   let subtree := (←Sym.simp f).getResultExpr f
    --   trace[Clap.Compile.simp.proc.monad.bind_assoc]
    --     m!"Subtree.\n{f}\n==>\n{subtree}"
    --   let u ← Sym.getLevelInType α
    --   let v ← Sym.getLevelInType β
    --   let w ← Sym.getLevelInType γ
    --   -- `f : α → m β | g : β → m γ | x : m α`
    --   let bind ← shareCommonInc <|
    --     mkApp4 (.const ``Option.bind [v, w]) β γ (←shareCommonInc (f.beta #[.bvar 0])) g
    --   let cont := Expr.lam `_assoc α bind .default
    --   let e' ← shareCommonInc <| mkApp4 (.const ``Option.bind [u, w]) α γ x cont
    --   trace[Clap.Compile.simp.proc.monad.bind_assoc]
    --     m!"\n{e}\n==>\n{e'}"
    --   -- Dbg.timeSince time "bind_assoc took:"
    --   return .step e' (←mkSorry (←mkEq e e') false)
    | Option.some _ x =>
      let e' ← shareCommonInc (g.beta #[x])
      trace[Clap.Compile.simp.proc.monad.bind_some]
        m!"\n{e}\n==>\n{e'}"
      return .step e' (←Sym.mkEqRefl e')
    | _ => return .rfl
    -- | _ =>
    --   -- addConstraint q(Nat)
    --   -- logInfo m!"res: {←getConstraints}" -- x >>= f
    --   let x' := (←Sym.simp x (←read).toMethods).getResultExpr x
    --   if isSameExpr x x' then
    --     trace[Clap.Compile.simp.proc.monad.top_level]
    --       m!"{checkEmoji} {x'}"
    --     return .rfl
    --   else
    --     trace[Clap.Compile.simp.proc.monad.top_level]
    --       m!"\n{x}\n==>ₗ\n{x'}"
    --   let g' := (←Sym.simp g).getResultExpr g
    --   trace[Clap.Compile.simp.proc.monad.top_level]
    --     m!"\n{g}\n==>ᵣ\n{g'}"
    --   let e' ← shareCommonInc <|
    --     mkApp4 (.const ``Option.bind [←Sym.getLevelInType α, ←Sym.getLevelInType γ]) α γ x' g'
    --   trace[Clap.Compile.simp.proc.monad.top_level]
    --     m!"\n{e}\n==>\n{e'}"
    --   return .step e' (←mkSorry (←mkEq e e') false)
  | _ =>
    return .rfl

def bind_eq_bind_sym {α} {β} := (Option.bind_eq_bind (α := α) (β := β)).symm

def compilerBindEqBind : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``bind_eq_bind_sym
  ]

def monadBindAssocSimple : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``Option.bind_assoc
  ]

def monads : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``monad,
  ]

-- def compilerAssoc : MetaM Sym.Simp.Methods :=
--   mkPreMethods #[
--     ``monadBindAssoc
--   ]

-- def compilerAssocPost : MetaM Sym.Simp.Methods :=
--   mkPostMethods #[
--     ``monadBindAssoc
--   ]

end General

namespace Vector



-- /--
-- Currently separate from the `vectorElemsOfMk` chain.
-- -/
-- def elemsOfColl (e : Expr) : Option (Collection × Array Expr × Expr) :=
--   match_expr e with
--   | Vector.mk t sz _ _ => (.Vector t sz, ·) <$> (vectorElemsOfMk e)
--   | Array.mk t _      => arrayElemsOfExpr' e >>= fun res ↦ .some (.Array t, spoon res)
--   | _                 => listElemsOfExpr' e >>= fun res ↦ .some (.List, spoon res)
--   where spoon := fun (arr, t, sz) ↦ (arr, t, toExpr sz)

-- def Collection.elemsOfExpr (e : Expr) : Option (Array Expr × Collection) :=
--   Collection.elems <$> Collection.ofExpr e

-- def _root_.Lean.Expr.listLitIsEmpty (e : Expr) : Bool :=
--   match_expr e with
--   | List.cons _ _ _ => false
--   | _ => true

-- def _root_.Lean.Expr.listLitHead (e : Expr) : Option Expr :=
--   match_expr e with
--   | List.cons _ hd _ => .some hd
--   | _ => .none

-- def _root_.Lean.Expr.listLitTail (e : Expr) : Option Expr :=
--   match_expr e with
--   | List.cons _ _ tl => .some tl
--   | _ => .none

-- def explode : MetaM Methods := do
--   return {
--     -- post := explodeVector
--     pre  := dontExplodeVector >> explodeVector
--   }

-- def _root_.Lean.Expr.foldlM? (e : Expr) : Option (List Expr) :=
--   match_expr e with
--   | Vector.foldlM _ β α _ _ f init xs => .some [α, β, f, init, xs]
--   | Array.foldlM α β _ _ f init xs _ _ => .some [α, β, f, init, xs]
--   | List.foldlM _ _ β α f init xs => .some [α, β, f, init, xs]
--   | _ => .none

-- def _root_.Lean.Expr.foldlMInfo? (e : Expr) : Option (List Expr) :=
--   match_expr e with
--   | Vector.foldlM m β α _ inst f init xs => .some [m, inst, α, β, f, init, xs]
--   | Array.foldlM α β m inst f init xs _ _ => .some [m, inst, α, β, f, init, xs]
--   | List.foldlM m inst β α f init xs => .some [m, inst, α, β, f, init, xs]
--   | _ => .none

/-
`a >>= λ a₁ : t₁ ↦ b >>= λ a₂ : t₂ ↦ c >>= λ a₃ : t₃ ↦ a₄ : m t₄` = `(#[(a, t₁), (b, t₂), (c, t₃)], t₄)`
-/
partial def _root_.Lean.Expr.sequenceBinds (e : Expr) : Array (Expr × Expr) :=
  go e #[]
  where
    go (e : Expr) (res : Array (Expr × Expr)) :=
    match_expr e with
    | Option.bind _ _ a f =>
      -- The upcoming lambda knows the type of `a`, insert a _dummy_
      go f (res.push (a, default))
    | _ =>
      match e with
      | .lam _ dom body _ =>
        let (a, _dummy) := res.back!
        -- We know the type of `a`, replace the _dummy_
        go body (res.take (res.size - 1) |>.push (a, dom))
      | _ =>
        res.push (e, default)

-- def mk_append_mk : Simproc := fun e ↦ do
--   let_expr HAppend.hAppend _ _ _ _ xs ys := e | return .rfl

--   let .some ⟨xsElems, xsC⟩ ← sequenced xs | return .rfl
--   let .some ⟨ysElems, ysC⟩ ← sequenced ys | return .rfl

--   let append := xsElems.append ysElems

--   -- `xs.type.t = ys.type.t` ∧ `xs.type.k = ys.type.k`
--   let .some appendListColl := Collection.ofExpr (←Sym.mkListLit xsC.type.t append.toList) | unreachable!
--   let instAdd := Expr.const ``instAddNat []
--   let inst ← shareCommonInc <| mkApp2 (.const ``instHAdd [0]) q(ℕ) instAdd
--   let .some szXs := xsC.type.sz | unreachable!
--   let .some szYs := ysC.type.sz | unreachable!
--   let sz := mkApp6 (.const ``HAdd.hAdd [0, 0, 0]) q(ℕ) q(ℕ) q(ℕ) inst szXs szYs
--   let .some appendVecColl := appendListColl.setSize sz |>.cast xsC.type.k | unreachable!
--   let e' ← appendVecColl.toExpr

--   trace[Clap.Compile.simp.proc.vector_mk_append_mk]
--     m!"\n{e}\n==>\n{e'}"

--   return .step e' (←mkSorry (←mkEq e e') false)

def append : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_append_mk
  ]

-- /-
-- do let x : t₁ ← a1
--    a2
--    let x ← do a3; a4; return 4
--    a3 x
-- -/ --> [(a1, t₁), (a2, t₂), (a3, t₃), (a4, t₄), (return 4, ℕ), a3]

-- partial def _root_.Lean.Expr.sequenceBindsL (e : Expr) : Array (Expr × Expr) :=
--   go #[e] #[]
-- where
--   go (todo : Array Expr) (done : Array (Expr × Expr)) : Array (Expr × Expr) :=
--     match todo.back? with
--     | .none => done
--     | .some e =>
--       let todo := todo.pop
--       match e.matchBindsE with
--       | .some (action, func) =>
--         match action.matchBindsE with
--         | .some (b, g) =>
--           go (todo.append #[func, g, b]) done
--         | _ =>
--           go (todo.push func) (done.push (action, default))
--       | _ =>
--         match e with
--         | .lam _ dom body _ =>
--           let done := done.modify done.size.pred fun (a, _) ↦ (a, dom)
--           go (todo.push body) done
--         | _ =>
--           go todo (done.push (e, default))

-- partial def _root_.Lean.Expr.sequenceBindsL (e : Expr) : Array (Expr × Expr) :=
--   go #[e] #[]
-- where
--   go (todo : Array Expr) (done : Array (Expr × Expr)) : Array (Expr × Expr) :=
--     match todo.back? with
--     | .none => done
--     | .some e =>
--       let todo := todo.pop
--       match_expr e with
--       | Option.bind _ _ a f =>
--         match_expr a with
--         | Option.bind _ _ b g =>
--           go (todo.push f |>.push g |>.push b) done
--         | _ =>
--           go (todo.push f) (done.push (a, default))
--       | _ =>
--         match e with
--         | .lam _ dom body _ =>
--           let done := done.modify done.size.pred fun (a, _) ↦ (a, dom)
--           go (todo.push body) done
--         | _ =>
--           go todo (done.push (e, default))


-- partial def _root_.Lean.Expr.sequenceBindsL (e : Expr) : Array (Expr × Expr) :=
--   go e #[]
--   where
--     go (e : Expr) (res : Array (Expr × Expr)) :=
--     match_expr e with
--     | Option.bind _ _ a f =>
--       -- TODO: TR the L-traverse
--       match_expr a with
--       | Option.bind _ _ b g =>
--         let res' := go b res
--         let res'' := go g res'
--         go f res''
--       | _ =>
--         -- The upcoming lambda knows the type of `a`, insert a _dummy_
--         go f (res.push (a, default))
--     | _ =>
--       match e with
--       | .lam _ dom body _ =>
--         let (a, _dummy) := res.back!
--         -- We know the type of `a`, replace the _dummy_
--         go body (res.pop.push (a, dom))
--       | _ =>
--         res.push (e, default)



-- -- (bind (bind (b : Option α) (g : α → Option β) : Option β) (f : β → Option γ) : Option γ)
-- -- TODO: use `chainActions`
-- def bindMyAssoc : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Option.bind β γ a f := e | return .rfl
--   let_expr Option.bind α β b g := a | return .rfl
--   let actions := a.sequenceBinds
--   if actions.isEmpty then throwError m!"empty nested do block"
--   let actions := actions.modify actions.size.pred fun (e, _) ↦ (e, γ)
--   let .lam _ _ body _ := f | throwError m!"expected lambda"
--   let (e', _) ← actions.foldrM (init := (body, γ)) fun (a₁, ta₁) (a₂, ta₂) ↦
--     bindActions a₁ ta₁ a₂ ta₂
--   -- let (e', time) ← timeS (Sym.shareCommon e')
--   -- logInfo m!"sharing took: {time}s"
--   let e ← Sym.shareCommon e'
--   return .step e' (←mkSorry (←mkEq e e') false)

-- def bindMyAssoc_set : MetaM Methods :=
--   mkPostMethods #[
--     ``bindMyAssoc
--   ]

-- def monads! : MetaM Sym.Simp.Methods :=
--   mkPreMethods #[
--     ``SymSets.General.monad, ``bindMyAssoc
--   ]

opaque eq0 (n : Nat) : Option Unit

-- circuit (vec : Vector 2 Nat)...
-- let x : List Nat := f x

-- /--
-- This is for the custom traversal.

-- TODO(untested, perf, needs restructuring)
-- -/
-- def foldlM_singlePass : Sym.Simp.Simproc := fun e ↦ do
--   let .some [α, β, f, init, xs] := e.foldlM? | return .rfl
--   /-
--   TODO(perf): With head|tail reasoning, we don't need to traverse the full list literal expr.
--               Using `sequenced` does just that.
--   -/
--   let .some (elems, ⟨⟨_, k, .some sz⟩, listExpr⟩) ← sequenced xs | return .rfl
--   let szSimped := (←Sym.simpWithGround sz).getResultExpr sz
--   match szSimped.nat? with
--   | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e} (TODO: Maybe this is ok.)"
--   | .some _szSimpedNat => -- TODO(check)
--     let u ← Sym.getLevelInType β
--     let v ← Sym.getLevelInType α
--     let w := u -- `Option : Type u ↦ Type u` preserves the universe
--     match elems with
--     | ⟨[]⟩ =>
--       let e' ← Sym.shareCommonInc <| mkAppN (.const ``Option.some [u]) #[β, init]
--       return .step e' (←mkSorry (←mkEq e e') false) (done := true)
--     | ⟨.cons x _xs⟩ =>
--       -- `f init x`
--       let head ← Sym.shareCommonInc <| mkApp2 f init x
--       -- `_xs` but as list literal
--       let .some xs := listExpr.listLitTail | unreachable!
--       -- TODO(check): I _think_ I got the universes right.
--       -- `List.foldlM f acc xs` where `acc` comes from the enclosing bind
--       let tail ← Sym.shareCommonInc <| mkApp3 (.const ``List.foldlM [u, w, v]) f (.bvar 0) xs
--       -- `bind head tail`
--       let bind ← Sym.shareCommonInc <| mkApp2 (.const ``Option.bind [v, u]) head tail
--       return .step bind (←mkSorry (←mkEq e bind) false)

-- /--
-- `[1, 2, 3, 4].foldlM f b` ==>
-- `f b 1 >>= λ next → f next 2 >>= λ next → f next 3 >>= λ next ↦ pure next`
-- -/
-- def unfold_generic_mk_foldlM : Sym.Simp.Simproc := fun expr ↦ do
--   let .some [inputType, outputType, f, init, collection] := expr.foldlM? | return .rfl
--   let .some (elems, ⟨⟨_, _, .some size⟩, _⟩) ← sequenced collection | return .rfl

--   trace[Clap.Compile.dbg]
--     m!"Unfold_generic_mk_foldlM\nelems:{elems}\nsize:{size}"

--   let u ← Sym.getLevelInType outputType
--   let v ← Sym.getLevelInType inputType

--   let szSimped := (←Sym.simpWithGround size).getResultExpr size
--   match szSimped.nat? with
--   | .none => throwError m!"{size} does not simplify to ground. Expr:\n{expr} (TODO: Maybe this is ok.)"
--   | .some 0 =>
--     -- For an empty collection, return `some init`
--     let expr' ← Sym.shareCommonInc <| mkAppN (.const ``Option.some [u]) #[outputType, init]
--     trace[Clap.Compile.dbg]
--       m!"Unfold_generic_mk_foldlM 0 branch\nexpr':{expr'}"
--     trace[Clap.Compile.dbg]
--       m!"\n{expr}\n==>\n{expr'}"
--     return .step expr' (←mkSorry (←mkEq expr expr') false)
--   | .some _szSimpedNat =>
--     -- `some next`
--     let chain_base ← Sym.shareCommonInc <| mkAppN (.const ``Option.some [u]) #[outputType, .bvar 0]

--     -- repeated `(f x elem).bind fun x => acc`
--     let chain := elems.foldr (
--       λ (elem: Expr) (acc: Expr) =>
--         let bind_lhs := mkApp2 f (.bvar 0) elem
--         let bind_rhs := Expr.lam `next outputType acc .default
--         let bind := mkApp4 (.const `Option.bind [v, u]) inputType outputType bind_lhs bind_rhs
--         bind
--     ) chain_base

--     let wrapped_chain := Expr.lam `init outputType chain .default

--     let reduced_chain := wrapped_chain.beta #[init]

--     let expr' ← Sym.shareCommonInc <| reduced_chain


--     trace[Clap.Compile.dbg]
--       m!"\n{expr}\n==>\n{expr'}"

--     return .step expr' (←mkSorry (←mkEq expr expr') false)

-- /--
--   `#v[a₁, a₂, ...].foldlM (init := x) f`
--   `f a₁ x >>= fun rest ↦ [a₂, ...].foldlM (init := rest) f`
-- -/
-- def foldlM_stagger : Sym.Simp.Simproc := fun e ↦ do
--   let .some [m, inst, α, β, f, init, collection] := e.foldlMInfo? | return .rfl
--   -- TODO(perf): `coll` not necessary in full
--   let .some ⟨_, listExpr⟩ := Collection.ofExpr collection | return .rfl
--   -- let us@([u, v, w]) := e.getAppFn.constLevels! | unreachable!
--   let u₁ ← Sym.getLevelInType β
--   let u₂ := u₁
--   let u₃ ← Sym.getLevelInType α
--   let listFold ← Sym.shareCommonInc <|
--     mkApp7
--       (.const ``List.foldlM [u₁, u₂, u₃])
--       m inst
--       β α f init listExpr
--   match_expr listExpr with
--   | List.cons _ hd tl =>
--     -- let theorems : Theorems := ({} : Theorems).insert (←mkTheoremFromDecl ``List.foldlM_cons)
--     -- let e' ← theorems.rewrite dischargeNone listFold
--     -- let e' := e'.getResultExpr e
--     let head ← Sym.shareCommonInc <| f.beta #[init, hd]
--     let tail ← Sym.shareCommonInc <| mkApp7 (.const ``List.foldlM [u₁, u₂, u₃])
--                                             m inst
--                                             β α f (.bvar 0) tl
--     let lambda ← Sym.shareCommonInc <| .lam `next β tail .default
--     -- TODO(perf): Hand-write the types I guess vOv.
--     let tailτ ← Sym.inferType tail
--     let tailτu ← Sym.getLevelInType tailτ
--     let e' ← Sym.shareCommonInc <| mkApp4 (.const ``Option.bind [u₁, tailτu]) β tailτ head lambda
--     trace[Clap.Compile.simp.proc.vector_foldlM_stagger]
--       m!"\n{e}\n==>\n{e'}"
--     let e' ← Sym.shareCommonInc <| Simp.wrapped (←Sym.inferType e') e'
--     return .step e' (←mkSorry (←mkEq e e') false) (done := true)
--   | _ =>
--     let e' := mkApp2 (.const ``Option.some [u₁]) β init
--     trace[Clap.Compile.simp.proc.vector_foldlM_stagger]
--       m!"\n{e}\n==>\n{e'}"
--     return .step e' (←mkSorry (←mkEq e e') false) (done := true)

def foldlM : MetaM Methods :=
  mkPreMethods #[
    ``Vector.foldlM_mk, ``List.foldlM_toArray,

    ``List.foldlM_cons, ``List.foldlM_nil
  ]

-- def foldlM_mk_post : MetaM Methods :=
--   mkPostMethods #[
--     ``foldlM_mk
--   ]

-- def foldlM_singlePass_s : MetaM Methods :=
--   mkPreMethods #[
--     ``foldlM_singlePass
--   ]

-- circuit (vec : Vector 2 Nat)...
-- let x : List Nat := f x

-- def getElem_mk : Sym.Simp.Simproc := fun e => do
--   /-
--   TODO(perf):
--   In vector, we can optimise by not enumerating all elements first,
--   and then taking the size of the final list.

--   Instead, we can simply traverse the first `i` conses, as we have the length apriori for the proof.
--   Or some such.
--   -/
--   let_expr GetElem.getElem _ _ _ _ _ vec n _ := e | return .rfl
--   let .some (elems, t) := Collection.elemsOfExpr vec | return .rfl
--   let .some sz := t.type.sz | unreachable!
--   let n := (←Sym.simpWithGround n).getResultExpr n
--   let .some i := Sym.getNatValue? n | return .rfl
--   if h : i < elems.size
--   then
--     let e' := elems[i]
--     return .step e' (←Sym.mkEqRefl e')
--   else
--     return .rfl

open SymSets

def toArray : MetaM Methods :=
  mkPostMethods #[
    ``Vector.toArray_mk
  ]

-- def getElem : MetaM Methods :=
--   mkPostMethods #[
--     ``getElem_mk
--   ]

def getElem_old : MetaM Methods :=
  mkPostMethods #[
    ``Vector.getElem_mk, ``List.getElem_toArray,

    ``List.getElem_cons_zero, ``List.getElem_cons_succ,
  ]

def map : MetaM Methods :=
  mkPostMethods #[
    ``Vector.map_mk, ``List.map_toArray,

    ``List.map_cons, ``List.map_nil,
  ] >> mapOptim
  where
    mapOptim : MetaM Methods := mkPreMethods #[``List.map_id]

-- def mapIdx_mk : Sym.Simp.Simproc := fun e => do
--   let_expr Vector.mapIdx inputType outputType sz f xs := e | return .rfl
--   let some (xs, _) := vectorElemsOfMk xs |
--     trace[Clap.Compile.simp.proc.vector_mapIdx_mk]
--       m!"rejected:\n{e}"
--     return .rfl

--   logInfo m!"Xs: {xs}"
--   let result ← Sym.mkListLit outputType (xs.mapIdx (f.beta #[mkNatLit ·, ·])).toList
--   logInfo m!"Result: {result}"
--   let e' ←mkVecLit outputType result sz
--   logInfo m!"e': {e'}"

--   return .step e' (←mkSorry (←mkEq e e') false)

-- def mapIdx : MetaM Methods :=
--   mkPostMethods #[
--     ``Vector.mapIdx_mk
--   ] >> SymSets.General.ground

def listOfArray (e : Expr) : Option Expr :=
  if e.isAppOf ``List.toArray || e.isAppOf ``Array.mk
  then .none
  else .some e.getAppArgs[1]!

def _root_.Lean.Expr.mapM? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.mapM _ α β _ _ f xs => .some [f, α, β, xs]
  | Array.mapM α β _ _ f xs    => .some [f, α, β, xs]
  | List.mapM _ _ α β f xs     => .some [f, α, β, xs]
  | _                          => .none

/--
TODO: No `MetaM` or better, how do I grab the universe of `α`?
      Of course we can just return `m n` from this, infer the `Sort` of `α` in the caller
      and reconstruct the `Vector` typpe this way, but it would make the interface of this dreary.
-/
def _root_.Lean.Expr.append? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | HAppend.hAppend α β γ _ xs ys => .some [α, β, γ, xs, ys]
  | _root_.Vector.append _ _ _ _ _ => panic! "Vector.append not implemented yet."
  | _ => .none

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
  if !isSameExpr sz szSimped then
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

-- open Compiler.Simp in
-- /--
-- Single step transformation. TODO: Does not play particularly nice with our top-level driver.
-- `Vector.mapM f #v[x₀, x₁, ..., xₘ]` ==>
-- `f x₀ >>= fun row₀ ↦ f x₁ >>= fun row₁ ↦ ... fun rowₘ ↦ .some #v[row₀, row₁, ..., rowₘ]`
-- -/
-- def _root_.Vector.mapM_mk_seq : Sym.Simp.Simproc := fun e ↦ do
--   let .some [f, _, β, xs] := e.mapM? | return .rfl
--   let .some (elems, ⟨⟨_, k, .some sz⟩, _⟩) ← sequenced xs | return .rfl
--   let szSimped := (←Sym.simpWithGround sz).getResultExpr sz
--   if !isSameExpr sz szSimped then
--     trace[Clap.Compile.simp.proc.vector_mapM_mk]
--       m!"Info: Processing `Vector _ ({sz})` of ground length {szSimped}. Request:\n{e}"
--   match szSimped.nat? with
--   | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e} (TODO: Maybe this is ok.)"
--   | .some szSimpedNat =>
--     let transformedList ← Sym.mkListLit β <| (List.range szSimpedNat).reverse.map .bvar
--     let .some transformedColl :=
--       Collection.ofExpr transformedList <&>
--       Collection.setSize (sz := szSimped) >>=
--       Collection.cast (t := k) | unreachable!
--     let transformedColl ← transformedColl.toExpr
--     let transformedCollT ← Sym.inferType transformedColl
--     let v ← Sym.getLevelInType transformedCollT
--     let transformedColl? :=
--       mkAppN (.const ``Option.some [v]) #[transformedCollT, transformedColl]
--     let transformedColl? ← Sym.shareCommonInc transformedColl?
--     let u ← Sym.getLevelInType β
--     /-
--     Start with `.some #[.bvar sz.pred, .bvar sz.pred.pred, ..., .bvar 0]`
--     Prefix a single lambda in each iteration.
--     -/
--     let e' ← (List.range szSimpedNat).foldrM (init := transformedColl?) fun i e ↦ do
--       let elem := elems[i]!
--       liftM ∘ Sym.shareCommonInc <|
--         mkAppN                                         -- `f vec[i] >>= fun row_{i} ↦ e`
--           (.const ``Option.bind [u, v])
--           #[
--             β, transformedCollT,                       -- implicits
--             ←Sym.shareCommonInc (f.beta #[elem]),      -- `f vec[i]`
--             .lam (binderInfo := .default)
--                  (binderName := .mkSimple s!"row_{i}")
--                  (binderType := β)
--                  (body       := e)                     -- `fun row_{i} ↦ e`
--           ]
--       -- Careful, `e` contains loose bvars until the very last iteration.
--     trace[Clap.Compile.simp.proc.vector_mapM_mk]
--       m!"\n{e}\n==>\n{e'}"
--     let proof ← mkSorry (←mkEq e e') false
--     -- Dbg.timeSince time "mapM_mk_cons took:"
--     trace[Clap.Compile.simp.proc.vector_mapM_mk]
--       m!"SEQ: {e'.sequenceBindsL}"
--     return .step e' proof

def reportMaxShared (e : Expr) (descr : String := "") : Sym.Simp.SimpM Unit := do
  try
    e.checkMaxShared
    logInfo m!"Is max shared.\n{descr}"
  catch _ =>
    logInfo m!"Not max shared.\n{descr}"

/--
Currently for vectors only.

`Vector.mapM f #v[x, ..v] = do`
  `let __do_lift ← f x`
  `let __do_lift_1 ← Vector.mapM f v`
  `pure (#v[__do_lift] ++ __do_lift_1)`
-/
def _root_.Vector.mapM_mk_single : Sym.Simp.Simproc := fun e ↦ do
  let_expr _root_.Vector.mapM m α β n mInst f vec := e | return .rfl
  let_expr _root_.Vector.mk _ sz arr _ := vec | return .rfl
  recordRuleDbg "mapM_mk_single"
  -- reportMaxShared e (descr := "BEGIN[mapM_mk_single]")
  let l ← arr.getAppArgs[1]?.getDM (unreachable!)
  let u ← Sym.getLevelInType β
  let_expr List.cons t hd tl := l |
    -- `#v[].mapM f ==> pure #v[]`
    -- TODO: Check universe
    let e' := mkApp2
                (.const ``Option.some [u])
                (mkApp2 (.const ``Vector [u]) β q(0))
                (←mkVecLit β (←Sym.mkListLit β []) q(0))
    trace[Clap.Compile.simp.proc.mapM_mk_single]
      m!"\n{e}\n==>\n{e'}"
    return .step e' (←mkSorry (←mkEq e e') false)
  let sz' ← Sym.simpWithGround sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e}"
  | .some szN =>
    /-
    No universe bump along the way
    `Vector.{u} {α : Type u}... : Vector.{u}`
    -/
    let v := u
    let w := u

    let hdSz := mkNatLit 1
    let tlSz := mkNatLit szN.pred

    -- `#v[__do_lift] ++ __do_lift_1`
    /-
      TODO(perf): Use the instance-less one for every typeclass'd operation.
    -/
    let append :=
      mkAppN
        (.const ``HAppend.hAppend [u, v, w]) #[
          (mkApp2 (.const ``Vector [u]) β hdSz),
          (mkApp2 (.const ``Vector [u]) β tlSz),
          (mkApp2 (.const ``Vector [u]) β (toExpr szN)),
          (mkApp3 (.const ``Vector.instHAppendHAddNat [u]) β hdSz tlSz),
          ←mkVecLit β (←Sym.mkListLit β [.bvar 1]) hdSz,
          .bvar 0
        ]

    -- let append := mkApp5 (.const ``_root_.Vector.append [u])
    --                 β hdSz tlSz (←mkVecLit β (←Sym.mkListLit β [.bvar 1]) hdSz) (.bvar 0)

    let tlVec ← mkVecLit α tl tlSz

    -- TODO: Check universes. `Vector` construction should preserve `u`.
    let v := u
    let w ← Sym.getLevelInType α
    let mapM := mkApp7 (.const ``Vector.mapM [u, v, w]) m α β tlSz mInst f tlVec
    -- TODO(perf): Hand write the type if helps, least of my problems
    let mapMT ← Sym.inferType mapM
    let_expr Option mapMT := mapMT | throwError m!"expected Option monad"
    let appendT ← Sym.inferType append
    let v ← Sym.getLevelInType mapMT

    let someAppend := mkApp2 (.const ``Option.some [u]) appendT append
    -- `Vector.mapM f tl >>= fun __do_lift_1 ↦ pure (#v[__do_lift] ++ __do_lift_1)`
    let innerBind :=
      mkApp4
        (.const ``Option.bind [u, v]) mapMT appendT mapM
        (.lam `_snd mapMT someAppend .default)
    /-
    TODO: Check the second universe, it's what `append : Vector.{u} (#[#1] ++ #0)` lives in, I think.
          Hence `u`. Or so I think.
    -/
    /-
      `let __do_lift ← f x >>= inner`
    -/
    let bind :=
      mkApp4
        (.const ``Option.bind [u, u])
        β
        appendT
        (←Sym.shareCommonInc (f.beta #[hd])) -- TODO(?): `Expr.app f hdVec` without reducing here?
        (.lam `fst t innerBind .default )
    let e' ← Sym.shareCommonInc bind
    -- let (e', time) ← timeS (Sym.shareCommonInc bind)

    -- logInfo m!"END[mapM_mk_single] Sym.shareCommonInc took {time}s"

    -- reportMaxShared e' (descr := "END[mapM_mk_single]")
    trace[Clap.Compile.simp.proc.mapM_mk_single]
      m!"\n{e}\n==>\n{e'}"

    return .step e' (←mkSorry (←mkEq e e') false)

/--
Currently for vectors only.

`Vector.mapM f #v[x, ..v] = do`
  `let __do_lift ← f x`
  `let __do_lift_1 ← Vector.mapM f v`
  `pure (#v[__do_lift] ++ __do_lift_1)`
-/
def _root_.Vector.mapM_mk_single_singlePass : Sym.Simp.Simproc := fun e ↦ do
  let_expr _root_.Vector.mapM m α β n mInst f vec := e | return .rfl
  let_expr _root_.Vector.mk _ sz arr _ := vec | return .rfl

  let l ← arr.getAppArgs[1]?.getDM (unreachable!)
  let u ← Sym.getLevelInType β
  let_expr List.cons t hd tl := l |
    -- `#v[].mapM f ==> pure #v[]`
    let e' := mkApp2 (.const ``Option.some [u]) β (←mkVecLit β (←Sym.mkListLit β []) q(0))
    trace[Clap.Compile.simp.proc.mapM_mk_single]
      m!"\n{e}\n==>\n{e'}"
    return .step e' (←mkSorry (←mkEq e e') false) (done := true)
  let sz' ← Sym.simpWithGround sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e}"
  | .some szN =>
    /-
    No universe bump along the way
    `Vector.{u} {α : Type u}... : Vector.{u}`
    -/
    let v := u
    let w := u

    let hdSz := mkNatLit 1
    let tlSz := mkNatLit szN.pred

    -- `#v[__do_lift] ++ __do_lift_1`
    /-
      TODO(perf): Use the instance-less one for every typeclass'd operation.
    -/
    let append :=
      mkAppN
        (.const ``HAppend.hAppend [u, v, w]) #[
          (mkApp2 (.const ``Vector [u]) β hdSz),
          (mkApp2 (.const ``Vector [u]) β tlSz),
          (mkApp2 (.const ``Vector [u]) β (toExpr szN)),
          (mkApp3 (.const ``Vector.instHAppendHAddNat [u]) β hdSz tlSz),
          ←mkVecLit β (←Sym.mkListLit β [.bvar 1]) hdSz,
          .bvar 0
        ]

    let tlVec ← mkVecLit α tl tlSz

    -- TODO: Check universes. `Vector` construction should preserve `u`.
    let v := u
    let w ← Sym.getLevelInType α
    let mapM := mkApp7 (.const ``Vector.mapM [u, v, w]) m α β tlSz mInst f tlVec
    -- TODO(perf): Hand write the type if helps, least of my problems
    let mapMT ← Sym.inferType mapM
    let appendT ← Sym.inferType append
    let v ← Sym.getLevelInType mapMT

    let someAppend := mkApp2 (.const ``Option.some [u]) appendT append

    -- `Vector.mapM f tl >>= fun __do_lift_1 ↦ pure (#v[__do_lift] ++ __do_lift_1)`
    let innerBind :=
      mkApp4
        (.const ``Option.bind [u, v]) mapMT appendT mapM
        (.lam `_snd mapMT someAppend .default)

    /-
    TODO: Check the second universe, it's what `append : Vector.{u} (#[#1] ++ #0)` lives in, I think.
          Hence `u`. Or so I think.
    -/
    /-
      `let __do_lift ← f x >>= inner`
    -/
    let bind :=
      mkApp4
        (.const ``Option.bind [u, u])
        β
        appendT
        (←Sym.shareCommonInc (f.beta #[hd])) -- TODO(?): `Expr.app f hdVec` without reducing here?
        (.lam `fst t innerBind .default )

    -- See the docs of `singlePass`
    let e' ← Sym.shareCommonInc (singlePass appendT bind)

    trace[Clap.Compile.simp.proc.mapM_mk_single]
      m!"\n{e}\n==>\n{e'}"

    return .step e' (←mkSorry (←mkEq e e') false) (done := true)

def mapM_singlePass : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk_single_singlePass
  ]

def mapM_singlePass_pre : MetaM Methods :=
  mkPreMethods #[
    ``Vector.mapM_mk_single_singlePass
  ]

  -- -- logInfo m!"Nodes: {←e.numObjs}"
  -- -- let α ← IO.monoMsNow
  -- let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .rfl
  -- let_expr _root_.Vector.mk _ sz arr _ := vec | return .rfl
  -- logInfo m!"e: {e}"
  -- unless arr.isAppOf ``List.toArray || arr.isAppOf ``Array.mk do return .rfl
  -- let l ← arr.getAppArgs[1]?.getDM (unreachable!)
  -- let_expr List.cons t hd tl := l | return .rfl
  -- let sz' ← Sym.simp sz
  -- match (sz'.getResultExpr sz).nat? with
  -- | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e}"
  -- | .some szN =>
  --   if szN == 0 then return .rfl
  --   let hdVec ← mkVecLit t (←Sym.mkListLit t [hd]) (mkNatLit 1)
  --   let tl ← mkVecLit t tl (toExpr (szN - 1))
  --   let appendHdTl ← if szN == 1 then pure hdVec else mkAppM ``HAppend.hAppend #[hdVec, tl]
  --   let_expr Vector _ szAppendHdTl := ←Sym.inferType appendHdTl | unreachable!
  --   let szAppendHdTlQ : Q(ℕ) := szAppendHdTl
  --   let szDesired : Q(ℕ) := toExpr szN
  --   let proof ← mkSorry q($szAppendHdTlQ = $szDesired) false
  --   -- logInfo m!"will try to cowboy cast: {appendHdTl}"
  --   -- let thatGuy ← cowboyCast appendHdTl szN
  --   let thatGuy := appendHdTl
  --   let thisGuy := appendHdTl
  --   let thisGuy := thatGuy
  --   let mapM ← mkAppM ``_root_.Vector.mapM #[f, thisGuy]
  --   let theMiddleBit ←
  --     if szN == 1
  --     then mkVecLit t (←Sym.mkListLit t [.bvar 1]) (mkNatLit 1)
  --     else pure <| mkAppN
  --           (.const ``HAppend.hAppend [
  --             ←getDecLevel (←Sym.inferType hdVec),
  --             ←getDecLevel (←Sym.inferType tl),
  --             ←getDecLevel (←Sym.inferType thisGuy)
  --           ]) #[
  --             ←Sym.inferType hdVec,
  --             ←Sym.inferType tl,
  --             ←Sym.inferType thisGuy,
  --             -- ←Sym.inferType appendHdTl,
  --             ←Sym.synthInstance (←mkAppM ``HAppend #[←Sym.inferType hdVec,←Sym.inferType tl,←Sym.inferType thisGuy,]),
  --             ←mkVecLit t (←Sym.mkListLit t [.bvar 1]) (mkNatLit 1),
  --             .bvar 0
  --           ]
  --   logInfo m!"theMiddleBit: {theMiddleBit}"
  --   let consMapM ←
  --     mkAppM ``Option.bind #[
  --       f.beta #[hd],
  --       -- Expr.app f hdVec,
  --       .lam `fst t
  --         (←mkAppM ``Option.bind #[
  --                    ←mkAppM ``Vector.mapM #[f, tl],
  --                    .lam `snd (←Sym.inferType tl)
  --                      (←mkAppM ``Option.some #[theMiddleBit])
  --                      .default
  --         ])
  --         .default
  --     ]
  --   logInfo m!"consMapM: {consMapM}"
  --   let e' ← Sym.shareCommonInc consMapM
  --   trace[Clap.Compile.simp.proc.vector_mapM_mk]
  --     m!"\n{e}\n==>\n{e'}"
  --   return .step consMapM (←mkSorry (←mkEq e mapM) false)

/--
`Vector.mapM_mk_singleton_append` is a part of `Vector.mapM_mk_append` to ensure that
the transformation `#v[a, b] ==> #v[a] ++ #v[b]` does not get undone by `Vector.mk_append_mk`.
-/
def mapM : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk

    -- ``Compiler.explodeVectorMapM
  ]

-- def mapM_seq : MetaM Methods :=
--   mkPostMethods #[
--     ``Vector.mapM_mk_seq
--   ]

def mapM_alt : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk_single
    -- ``Compiler.explodeVectorMapM
  ]

#check List.map_cons
-- def mapM_test : MetaM Methods :=
--   mkPostMethods #[
--     ``Vector.mapM_mk_cons, ``Compiler.explodeVectorMapM
--   ]

def mk_zipWith_mk : Sym.Simp.Simproc := fun e => do
  let_expr Vector.zipWith _ _ γ n f xs ys := e | return .rfl

  let some (xs, _, szXs) := vectorElemsOfMk xs | return .rfl
  let some (ys, _, szYs) := vectorElemsOfMk ys | return .rfl

  if !isSameExpr szXs szYs then
    trace[Clap.Compile.simp.proc.vector_mk_zipWith_mk]
      m!"Info:\nxs.size = {szXs}\nys.size = {szYs}"

  let result ← Sym.mkListLit γ (xs.zipWith (f.beta #[·, ·]) ys).toList

  /-
  Doesn't matter which size we choose, we always have to check at consumption cast.
  Here, we take `n`, which need not be _syntactically_ equal to `szXs` nor `szYs`.

  TODO: Ideally, there would be a normalising step that would process all vector sizes,
  but it gets really tricky with casts.
  -/
  let e' ← mkVecLit γ result n

  trace[Clap.Compile.simp.proc.vector_mk_zipWith_mk]
    m!"\n{e}\n==>\n{e'}"

  return .step e' (←mkSorry (←mkEq e e') false)

def zipWith : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_zipWith_mk,
    -- ``List.zipWith_toArray,

    -- ``List.zipWith_cons_cons, ``List.zipWith_nil_left, ``List.zipWith_nil_right,

    -- ``Compiler.explodeVectorZipWith
  ]

def take : MetaM Methods :=
  mkPostMethods #[
    ``Vector.take_mk, ``List.take_toArray,

    ``List.take_succ_cons, ``List.take_nil, ``List.take_zero,

    -- ``Compiler.explodeVectorTake
  ]

def drop : MetaM Methods :=
  mkPostMethods #[
    ``Vector.drop_mk, ``_root_.List.drop_toArray,

    ``List.drop_succ_cons, ``List.drop_zero, ``List.drop_nil, ``List.drop_zero,

    -- ``Compiler.explodeVectorDrop
  ]

def _root_.List.replicate_toArray {α : Type} {n} {v} := (List.toArray_replicate (α := α) n v).symm

def replicate : MetaM Methods :=
  mkPostMethods #[
    ``Vector.replicate_eq_mk_replicate, ``List.replicate_toArray,

    ``List.replicate_succ, ``List.replicate_zero
  ]

def extract : MetaM Methods :=
  mkPostMethods #[
    ``Vector.extract_mk, ``List.extract_toArray,

    ``List.extract_eq_take_drop
  ] >> drop >> take >> SymSets.General.ground


-- def size : MetaM Methods :=
--   mkPostMethods #[
--    ``Vector.size_toArray, ``List.size_toArray,

--    ``List.length_cons, ``List.length_nil
--   ]

def _root_.Lean.Expr.foldr? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.foldr α β _ f init xs => .some [α, β, f, init, xs]
  -- `start = xs.size` ∧ `stop = 0`
  | Array.foldr α β f init xs start stop => .some [α, β, f, init, xs]
  | List.foldr α β f init xs => .some [α, β, f, init, xs]
  | _ => .none

/--
TODO: We ignore start/stop on purpose for the time being.
      `Sym` does not play nice with `List.foldr_toArray` and `List.foldr_toArray'` sometimes...

      This is currently unprovable.
-/
-- def foldr_toArrayButSane : Sym.Simp.Simproc := fun e => do
--   let_expr Array.foldr α β f init xs _ _ := e | return .rfl
--   let .some ⟨_, xs⟩ := Collection.ofExpr xs | throwError m!"cannot foldr:\n{xs} in:\n{e}"
--   let e' ← Sym.shareCommonInc <| mkApp5 (.const ``List.foldr e.getAppFn.constLevels!) α β f init xs
--   return .step e' (←mkSorry (←mkEq e e') false)

-- def foldr : MetaM Methods :=
--   mkPostMethods #[
--     ``Vector.foldr_mk, ``foldr_toArrayButSane,

--     ``List.foldr_cons, ``List.foldr_nil,
--   ] >> size >> SymSets.General.ground

-- def sum : MetaM Methods :=
--   mkPostMethods #[
--     ``Vector.sum_eq_foldr
--   ] >> foldr

def unwrap : Sym.Simp.Simproc := fun e ↦ do
  let_expr Simp.clapwrap _ e := e | return .rfl
  return .rfl (done := true)

-- def unwrap_s : MetaM Methods :=
--   mkPreMethods #[
--     ``Clap.Compiler.SymSets.Vector.unwrap
--   ]

-- def set_mk : Sym.Simp.Simproc := fun e => do
--   let_expr Vector.set t sz xs i x h := e | return .rfl
--   let some (xs, _, _) := vectorElemsOfMk xs | return .rfl
--   let iGround := (←simpWithGround i).getResultExpr i
--   match Sym.getNatValue? iGround with
--   | .none => throwError m!"Not ground: {iGround}. Request:\n{e}"
--   | .some iNat =>
--     -- TODO: I guess we can `Vector.set` with `h`.
--     let result ← Sym.mkListLit t (xs.set! iNat x).toList
--     let e' ← mkVecLit t result sz
--     trace[Clap.Compile.simp.proc.vector_set_mk]
--       m!"\n{e}\n==>\n{e'}"
--     return .step e' (←mkSorry (←mkEq e e') false)

def set : MetaM Methods :=
  mkPostMethods #[
    ``Vector.set_mk
    -- ``List.set_toArray,

    -- ``List.set_cons_succ, ``List.set_cons_zero,
  ]

def set_pre : MetaM Methods :=
  mkPreMethods #[
    ``Vector.set_mk
    -- ``List.set_toArray,

    -- ``List.set_cons_succ, ``List.set_cons_zero,
  ]


  -- let t ← Sym.inferType e
  -- let_expr Vector t sz := t | return .rfl
  -- unless e.isFVar do return .rfl
  -- let sz' ← Sym.simpWithGround sz
  -- match (sz'.getResultExpr sz).nat? with
  -- | .none => throwError m!"{sz} does not simplify to ground.\nExpr:\n{e}"
  -- | .some _n => let explodedVec ← (sequenceAsVecExpr e t (sz'.getResultExpr sz)).run'
  --               trace[Clap.Compile.simp.proc.kaboom] m!"{who}"
  --               -- trace[Clap.Compile.simp.proc.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
  --               return .step explodedVec (←mkSorry (←mkEq e explodedVec) false)

-- private def explodeWrapper {α : Type} {k} (inner : Vector α k) (who : String := ""): Vector α k := inner

-- private def unwrap : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Simp.clapwrap _ e := e | return .rfl
--   return .rfl (done := true)

-- def explode! : Sym.Simp.Simproc := fun e ↦ do
--   let_expr explodeWrapper τ sz e who := e | return .rfl
--   unless e.isFVar do return .rfl
--   let sz' ← Sym.simpWithGround sz
--   let sz' := sz'.getResultExpr sz
--   match Sym.getNatValue? sz' with
--   | .none => throwError m!"[unreachable]\n{sz} does not simplify to ground in:\n{e}"
--   | .some _n => let explodedVec ← (sequenceAsVecExpr e τ sz').run'
--                 trace[Clap.Compile.simp.proc.kaboom] m!"{who}"
--                 -- trace[Clap.Compile.simp.proc.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
--                 return .step explodedVec (←mkSorry (←mkEq e explodedVec) false)


-- private def wrappedInExplosives (τ sz who : Expr) : Sym.Simp.SimpM Expr := do
--   let τu ← Sym.getLevelInType τ
--   let vectorτ ← Sym.shareCommonInc <| mkApp2 (.const ``Vector [τu]) τ sz
--   Sym.shareCommonInc <| mkApp4 (.const ``explodeWrapper [τu]) τ sz vectorτ who

-- private def wrapInExplosives (τ sz who e : Expr) : Sym.Simp.SimpM Result := do
--   let e' ← wrappedInExplosives τ sz who
--   return .step e' (←mkSorry (←mkEq e e') false)

-- def explode? : Sym.Simp.Simproc := fun e ↦ do
--   if let .some [α, β, γ, xs, ys] := e.append?
--   then
--     let .some xs := Collection.elemsOfExpr xs | return .rfl
--     let .some ys := Collection.elemsOfExpr ys | return .rfl
--     return mkApp
--   else
--     return .rfl


def processWrapped : Sym.Simp.Simproc := fun e ↦ do
  let_expr Simp.clapwrap _ e := e | return .rfl
  return .rfl (done := true)

def wrapped : MetaM Methods :=
  mkPreMethods #[``processWrapped]

-- def unfold_generic_collection_functions_pre : MetaM Methods :=
--   mkPreMethods #[
--     -- `Clap.Compiler.SymSets.Vector.unfold_generic_mk_foldlM,
--     ``Clap.Compiler.SymSets.Vector.foldlM_stagger,
--     `Clap.Compiler.SymSets.Vector.getElem_mk,
--     `Clap.Compiler.SymSets.Vector.set_mk
--   ]

-- def unfold_generic_collection_functions_post : MetaM Methods :=
--   mkPostMethods #[
--     -- `Clap.Compiler.SymSets.Vector.unfold_generic_mk_foldlM,
--     ``Clap.Compiler.SymSets.Vector.foldlM_stagger,
--     `Clap.Compiler.SymSets.Vector.getElem_mk,
--     `Clap.Compiler.SymSets.Vector.set_mk
--   ]

-- def foldlM_stagger_post : MetaM Methods :=
--   mkPostMethods #[
--     ``Clap.Compiler.SymSets.Vector.foldlM_stagger,
--   ]

end Vector

-- namespace List

-- def reduceRange : Sym.Simp.Simproc := fun e ↦ do
--   let_expr _root_.List.range k ← e | return .rfl
--   match (←Sym.simp k).getResultExpr k |>.nat? with
--   | .none => logError m!"{(←Sym.simp k).getResultExpr k} is not ground"
--              return .rfl
--   | .some n => let l := _root_.List.range n
--                let e' ← Sym.shareCommonInc (Lean.toExpr l)
--                return .step e' (←Sym.mkEqRefl e')

-- def range : MetaM Methods := do
--   return {
--     post := reduceRange
--   }

-- end List

end

abbrev Simplifier := Expr → Sym.Simp.SimpM Expr

/--
- `a : Option α` = `⟨uα, α, a⟩`
-/
structure Action where
  u : Level
  α : Expr
  a : Expr
  deriving Repr

def Action.simplifyUsing (a : Action) (simp : Simplifier) : Sym.Simp.SimpM Action :=
  let ⟨u, α, a⟩ := a
  simp a >>= (return ⟨u, α, ·⟩)

/--
- `f : α → Option β` = `⟨uα, uβ, α, β, f⟩`
-/
structure Cont where
  u : Level
  v : Level
  α : Expr
  β : Expr
  f : Expr
  deriving Repr

/--
- `Option.bind.{u, v} α β a f`
-/
structure Bind where
  u  : Level
  v  : Level
  α  : Expr
  β  : Expr
  aₗ : Expr
  aᵣ : Expr
  deriving Repr

def Bind.toExpr (bind : Bind) : Expr :=
  let ⟨u, v, α, β, a, f⟩ := bind
  mkApp4 (.const ``Option.bind [u, v]) α β a f

def Bind.toCont (bind : Bind) : Cont :=
  let ⟨u, v, α, β, _, f⟩ := bind
  ⟨u, v, α, β, f⟩

def Bind.explode (bind : Bind) : Action × Cont :=
  let ⟨u, v, α, β, a, f⟩ := bind
  (⟨u, α, a⟩, ⟨u, v, α, β, f⟩)

/--
NB: `Bind.bind` better be instantiating `Option`.
-/
private def _root_.Lean.Expr.matchBinds (e : Expr) : Sym.SymM (Option Bind) := do
  match_expr e with
  | Bind.bind _ _ α β a f => return .some ⟨←Sym.getLevelInType α, ←Sym.getLevelInType β, α, β, a, f⟩
  | Option.bind   α β a f => return .some ⟨←Sym.getLevelInType α, ←Sym.getLevelInType β, α, β, a, f⟩
  | _                     => return .none

private def _root_.Lean.Expr.isUnital (e : Expr) : Bool :=
  match_expr e with
  | Unit  => true
  | PUnit => true
  | _     => false

structure ActionWithResult where
  action : Expr
  result : Expr

abbrev InProgressExpr := ActionWithResult ⊕ Expr

def logRewrite (e e' : Expr) (decorate : String := "") : MessageData :=
  m!"\n{e}\n={decorate}=>\n{e'}"

-- def inlineFirst (e : Expr) : Expr :=
--   match e.matchBindsEInfo with
--   | .some (levels, #[α, β, a, f]) =>
--     let tail := mkApp4 (.const ``Option.bind levels) α β a f
--     _
--   | _ => e


-- def firstAction (e : Expr) : Expr × Option Expr :=
--   go e
--   where
--     go (e : Expr) (rest : Option Expr) : Expr × Option Expr :=
--     match e.matchBindsE with
--     | .none => (e, rest)
--     | .some (a, f) => let res := go a ()

-- mutual

-- private partial def down (reduce reduceOuter : Simplifier)
--                          (stack : List InProgressExpr) (todo : Expr)
--                          : Sym.Simp.SimpM Expr := do
--   SymSets.General.inDebugOnly (do modifyDbgState fun σ ↦ {σ with numDown := σ.numDown + 1})
--   -- See the docs of `unwrapped`
--   -- let todo := unwrapped todo
--   let .some ⟨_, _, _, β, _, _⟩ ← todo.matchBinds | return todo
--   let binds := todo.sequenceBindsL -- do A; B; let x ← C; D; E ==> [A, B, C, D, E]
--   logInfo m!"e: {todo}\nbinds:"
--   let simpedBinds ← binds.mapM fun (action, τ) ↦ do
--     -- let (simped, time) ← Dbg.timeS (reduce action)
--     -- trace[Clap.Compile.down] logRewrite action simped
--     -- SymSets.General.inDebugOnly do trace[Clap.Compile.dbg] m!"simp took {time}s"
--     -- return (simped, τ)
--     return (action, τ)
--   let binds := SymSets.Vector.chainActions β simpedBinds
--   logInfo m!"binds: {←binds}"
--   binds

--   -- if let .some ⟨_, _, _, _, a, f⟩ ← todo.matchBinds -- TODO(perf): Propagate the rest.
--   -- then
--   --   trace[Clap.Compile.down] m!"\npush [→]:\n{f}\ngo [↓]:\n{a}"
--   --   down reduce reduceOuter (.inr f :: stack) a
--   -- else
--   --   let (simped, time) ← Dbg.timeS (reduce todo)
--   --   inDebugOnly (do
--   --     trace[Clap.Compile.dbg] m!"simp [↓] took {time}s"
--   --     modifyDbgState fun σ ↦ {σ with cumulativeSimpTimeDown := σ.cumulativeSimpTimeDown + time}
--   --   )
--   --   if !Sym.isSameExpr simped todo
--   --   then
--   --     trace[Clap.Compile.simp] "[↓] {checkEmoji}\n{todo}\n==>\n{simped}"
--   --     trace[Clap.Compile.down] "\ngo [↓]:\n{simped}"
--   --     down reduce reduceOuter stack simped
--   --   else
--   --     trace[Clap.Compile.simp.fail] "[↓] {crossEmoji}\n{todo}"
--   --     trace[Clap.Compile.down] "\ngo [↑]:\n{todo}"
--   --     -- match ←isGroundTerm todo with
--   --     -- | .some e => trace[Clap.Compile.simp.warnDownNotGround] "{stopEmoji} [↓] stopped:\n{e}"
--   --     -- | .none => pure ()
--   --     up reduce reduceOuter stack todo

-- private partial def up (reduce reduceOuter : Simplifier)
--                        (stack : List InProgressExpr) (done : Expr) : Sym.Simp.SimpM Expr := do
--   SymSets.General.inDebugOnly (modifyDbgState fun σ ↦ {σ with numUp := σ.numUp + 1})
--   match stack with
--   | [] =>
--     trace[Clap.Compile.up] "Done"
--     return done
--   | .inr e :: stack => do
--     -- TODO: Bad idea to use the One! guy, need to eta-expand if need be if so...
--     lambdaTelescope e fun arg body ↦ do
--       let #[arg] := arg | unreachable!
--       trace[Clap.Compile.up] "\npush [←]:\n{(done, arg)}\ngo [↓]:\n{body}"
--       down reduce reduceOuter (.inl {action := done, result := arg} :: stack) body
--   | .inl ⟨a, result⟩ :: stack => do
--     let bind ← mkBindWith a result done
--     let up := up reduce reduceOuter stack
--     let lamArgT ← Sym.inferType result -- TODO(perf): Propagate universe/type info from `matchBinds`.
--     if lamArgT.isUnital
--     then trace[Clap.Compile.up] "\ngo [↑]:\n{bind}"
--          up bind
--     else trace[Clap.Compile.simp] "Binding value: {result} in {bind}"
--          let (simped, time) ← Dbg.timeS (reduceOuter bind)
--         --  let (simped, time) := (bind, 0)
--          SymSets.General.inDebugOnly (do
--            trace[Clap.Compile.dbg] m!"simp [↑] took {time}s"
--            trace[Clap.Compile.dbg] m!"\n{bind}\n==>\n{simped}"
--            modifyDbgState fun σ ↦ {σ with cumulativeSimpTimeUp := σ.cumulativeSimpTimeUp + time}
--          )
--          -- TODO(semantics): Ok we simped, so what?
--          if !Sym.isSameExpr simped bind
--          then trace[Clap.Compile.simp] "[↑] {checkEmoji}\n{bind}\n==>\n{simped}"
--          else trace[Clap.Compile.simp.fail] "[↑] {crossEmoji}\n{bind}"
--          trace[Clap.Compile.up] "\ngo [↑]:\n{simped}"
--          up simped
--   where mkBindWith (a result k : Expr) : Sym.Simp.SimpM Expr := do
--     -- TODO(perf): Propagate universe/type info from `matchBinds`.
--     -- logInfo m!"a: {a}\nresult: {result}\nk: {k}"
--     let α ← result.fvarId!.getType
--     let u ← Sym.getLevelInType α
--     let β ← Sym.inferType k
--     let_expr Option t' := β | throwError m!"Body return not in `Option. Shouldn't be happening."
--     let v ← Sym.getLevelInType t'
--     let f ← Sym.shareCommonInc (←Sym.mkLambdaFVarsS #[result] k)
--     Sym.shareCommonInc <| mkApp4 (.const ``Option.bind [u, v]) α β a f

-- end

-- def compile (e : Expr) (simpset : Sym.Simp.Methods := default) : Sym.Simp.SimpM Expr := do
--   let simpset! ← SymSets.Vector.monads! >> return simpset
--   let e ← Compiler.Simp.preprocessExpr e
--   lambdaTelescope e fun args e ↦ do
--     let compiled ← down
--       (reduce      := Compiler.Simp.simplify simpset!)
--       (reduceOuter := Compiler.Simp.simplify simpset!)
--       -- (reduceOuter := Compiler.Simp.simplify simpset)
--       (stack       := [])
--       (todo        := e)
--     SymSets.General.inDebugOnly do trace[Clap.Compile.dbg] m!"σ: {←(←getDbgState).pretty}"
--     Sym.shareCommonInc (←mkLambdaFVars args compiled)

-- def compileExample (ex : Name) (simpset : Sym.Simp.Methods := default) (args : Array Expr := #[]) : Sym.Simp.SimpM Expr := do
--   -- withTraceNode `Clap.Compile.simp.proc (fun e ↦ return m!"") do
--   let e := ((←getEnv).find? ex).get!.value!.beta args
--   compile e simpset

def compileJustSym (e : Expr) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Expr := do
  let e ← Compiler.Simp.preprocessExpr e
  let res ← lambdaTelescope e fun args e ↦ do
    let time ← IO.monoMsNow
    let compiled ← Compiler.Simp.simplify simpset e
    Dbg.timeSince time "Compilation took:"
    let σ ← getDbgState
    logInfo m!"{←σ.pretty}"
    Sym.mkLambdaFVarsS args compiled
  Sym.shareCommonInc res

def compileExampleJustSym (ex : Name) (simpset : Sym.Simp.Methods) (args : Array Expr := #[]) : Sym.Simp.SimpM Expr := do
  -- withTraceNode `Clap.Compile.simp.proc (fun e ↦ return m!"") do
  let e := ((←getEnv).find? ex).get!.value!.beta args
  compileJustSym e simpset

open SymSets in
elab "compile_just_sym" "[" simps:ident,* "]" : tactic => do
  let simps ← simps.getElems.mapM fun s ↦ realizeGlobalConstNoOverload s.raw
  let methods ← simps.mapM (liftM ∘ Simp.API.getMethodsM)
  let methods ← liftM <| methods.foldl (fun method acc ↦ method >> acc) (pure {})
  Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    let time ← IO.monoMsNow
    let res ← (← Sym.simpGoal mvarId methods).toOption
    logInfo m!"compile_just_sym took {Dbg.timeInSecondsOfMs time (←IO.monoMsNow)}s"
    return res

-- def reportAttempt : Sym.Simp.Simproc := fun e ↦ do
--   discard bump
--   return .rfl

def rewriteReport : Sym.Simp.Simproc := fun e ↦ do
  let stuff ← Sym.Simp.mkTheoremFromDecl `Clap.Compiler.ExampruSym.a
  let res ← stuff.rewrite e
  match res with
  | .rfl .. => return res
  | .step .. =>
    logInfo m!"Did the rewrite"
    return res

-- bind (bind (bind x fun y₂ ↦ g (fun y₄ ↦ y₄)) fun y₃ ↦ g') fun y ↦ bind x₁ fun y₁ ↦ bind x₂ g''
-- [(x, fun y ↦ x), ..., ..., ] -- List.cons
/-
do
  do
    do
      x
      do
-/

-- elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
--   resetCounter
--   -- let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeNone
--   -- let methods : Sym.Simp.Methods := {
--   --   pre  := fun _ ↦ return .rfl
--   --   post := reportAttempt >> rewriteReport
--   -- }
--   let methods : Sym.Simp.Methods := {
--     pre  := fun _ ↦ return .rfl
--     post := reportAttempt >> Clap.Compiler.SymSets.General.betaReduce >> rewriteReport
--   }
--   Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
--     let mvarId ← Sym.preprocessMVar mvarId
--     let time ← IO.monoMsNow
--     let res ← (← Sym.simpGoal mvarId methods).toOption
--     logInfo m!"sym_simp took {Dbg.timeInSecondsOfMs time (←IO.monoMsNow)}s"
--     logInfo m!"this many times: {←getCounter}"
--     return res

def eq0 (e : Nat) : Option Unit := .some ()

opaque f : Option Unit

def tt : Option Unit :=
  Option.bind (eq0 0) fun _ ↦
  Option.bind
    (/- _ ↦-/Option.bind f
     fun _ ↦ Option.bind (.some 4)
     fun x ↦ Option.bind (.some <| x + 1)
     fun y ↦ .some <| y + x + x + 2) fun y ↦
  eq0 y

/-
ind_assoc:
(eq0 0).bind fun a =>
  f.bind fun a => (some 4).bind fun a => (some (a + 1)).bind fun y => (some (y + 2)).bind fun y => eq0 y

compile:
(eq0 0).bind fun x =>
  f.bind fun a => (some 4).bind fun a => (some (a + 1)).bind fun a => (some (a + 2)).bind fun a => eq0 a
-/

def tt' : Option Unit :=
  Option.bind (eq0 0) fun _ ↦
  Option.bind f fun _ ↦
  Option.bind (.some 4) fun x ↦
  Option.bind (.some <| x + 1) fun y ↦
  Option.bind (.some <| y + 2) fun y ↦
  eq0 y

def ppMonad (e : Expr) : MetaM Expr := do
  let pretty ← Sym.simp e (←General.compilerBindEqBind) |>.run
  return pretty.getResultExpr e

/-- a.k.a tablespoon -/
def liftExpr (m : Sym.Simp.SimpM Expr) : MetaM Expr := do
  m.run' {} |>.run

def spoon (m : Sym.Simp.SimpM Expr) (pretty := true) : MetaM Unit := do
  let compiled ← liftExpr m
  if pretty then
    let pretty ← ppMonad compiled
    logInfo m!"Compiled:\n{pretty}"
  else
    logInfo m!"Compiled:\n{compiled}"

open Sym in
/--
Applies hash-consing to `e`. Recall that all expressions in a `grind` goal have
been hash-consed. We perform this step before we internalize expressions.
-/
def shareCommon (e : Expr) : Sym.SymM Expr := do
  let share ← modifyGet fun s => (s.share, { s with share := {} })
  let (e, share) := shareCommonAlpha e share
  modify fun s => { s with share }
  return e

open Sym.Simp in
public def simpLambda' (simpBody : Simproc) (e : Expr) : Sym.Simp.SimpM Result := do
  lambdaTelescope e fun xs b => withFreshTransientCache do
    main xs (← shareCommon b)
where
  main (xs : Array Expr) (b : Expr) : Sym.Simp.SimpM Result := do
    let σ ← get
    let σ := σ.transientCache
    logInfo m!"START"
    for (k, v) in σ do
      logInfo m!"{k.expr} → {v.getResultExpr default}"
    logInfo m!"THE END"
    -- Propagate `cd` from the body: in another context the body might simplify differently.
    match (← simpBody b) with
    | .rfl _ cd => return mkRflResultCD cd
    | .step b' h _ cd =>
      let h ← mkLambdaFVars xs h
      let e' ← shareCommon (← mkLambdaFVars xs b')
      return .step e' (←mkSorry (←mkEq e e') false) (contextDependent := cd)

def ex₈ (n : ℕ) (vec : Vector Nat n) : Option Unit := do
  let x ← (do let _ ← eq0 2; let X ← vec.mapM (fun x ↦ (eq0 (x + 42) : Option _)); return 4)
  eq0 x

opaque share : Nat → Option Nat

def ex₉ {n : Nat} (vec : Vector Nat n) : Option Unit := do
  let x ← (do let _ ← eq0 2; let x ← vec.mapM (fun x ↦ (share (x + 42) : Option _)); return x)
  let _ ← x.mapM eq0

-- set_option maxRecDepth 1024 in
-- set_option trace.Clap.Compile.dbg true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile true in
-- #eval do
--   let (e, time) ← Dbg.timeS <| compileExampleJustSym (args := #[toExpr 10]) ``ex₉
--     (←(
--       mapM >>
--       getElem >>
--       append >>
--       explode -- >> monads -- >> zeta >> monads >> explode
--     >> compilerAssoc
--     -- >> bindMyAssoc_set
--     >> monads
--     -- mapM_alt
--     )) |>.run' {} |>.run
--   logInfo m!"time: {time}"
--   -- let e' := Sym.simp e {}
--   let e' := Sym.simp e (←compilerBindEqBind)
--   let e' ← e'.run

--   logInfo m!"e: {e'.getResultExpr e}"
--   -- logInfo m!"{←(getAndResetDbgState)}"

-- set_option Clap.traversalDbg true
-- set_option trace.Clap.Compile.dbg false
-- def bench : MetaM Unit := do
--   let simpset := (←(SymSets.Vector.wrapped >> mapM_mk >> explode >> compilerAssoc))
--   -- let simpset := (←(mapM_singlePass >> zeta >> explode))
--   let inputSizes := (Array.range 2).map (10 * 2^·)
--   let timings ← inputSizes.mapM fun inputSize ↦ do
--     let res ← Dbg.timeS <| (compileExample ``ex₉ simpset (args := #[mkNatLit inputSize])).run' {} |>.run
--     let σ ← getAndResetDbgState
--     return (inputSize, res, σ)
--   for (n, (compiled, time), dbgState) in timings do
--     logInfo m!"ex₈[{n}] took {time}s"
--     logInfo m!"dbg: {←dbgState.pretty}"

--     logInfo m!"{←ppMonad compiled}"

-- #eval bench

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

end ExpressionAnalysis

namespace Sets

namespace Structural

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
  unless coll.isFVar && (←inferType coll).isAppOf ``Vector do return .rfl
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
  General.control >>
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
  foldr
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
    (``Sets.Functional.betaReduce, .Pre),
    (``Sets.Functional.zetaReduce, .Pre)
  ]

end Functional

end Sets

open Sets in
partial def consiliumMagnum (e : Expr)
                            (extraPasses: MetaM Sym.Simp.Methods)
                            : Sym.Simp.SimpM Expr := do
  (·.1) <$> ire e 1
  where
    simp (e : Expr) (symset : Sym.Simp.Methods) : Sym.Simp.SimpM ExprChanged? := do
      let e' ← Sym.simp e symset <&> (·.getResultExpr e)
      return (e', !Sym.isSameExpr e e')

    consiliumRecursus: Sym.Simp.Simproc := fun expr ↦ do
      let .some (a, _) := expr.bind? | return .rfl
      let .some (_, _) := a.bind? | return .rfl
      let actions ← Sets.Structural.sequenceActions' expr
      logInfo m!"Calling consiliumMagnum on: {actions}"
      let simpedActions ← actions.mapM (consiliumMagnum · extraPasses)
      logInfo m!"Got out: {simpedActions}"
      let e' ← Sets.Structural.chainActionsInferType simpedActions
      return .step e' (←mkSorry (←mkEq e e') false)

    consiliumStructurale (e : Expr) : Sym.Simp.SimpM ExprChanged? := do
      simp e (←(
        (pure ({
          pre := consiliumRecursus
          post := fun _ ↦ pure (.rfl)
        }): MetaM Sym.Simp.Methods) >>
        Structural.structural
      ))

    consiliumFunctionale (e : Expr) : Sym.Simp.SimpM ExprChanged? := do
      simp e (←Functional.functional)

    consiliumGenerale (e : Expr) : Sym.Simp.SimpM ExprChanged? := do
      simp e (←General.general)

    consiliumExplicare (e : Expr) : Sym.Simp.SimpM ExprChanged? := do
      simp e (←extraPasses)

    ire (e : Expr) (numPasses : ℕ) : Sym.Simp.SimpM ExprIter := do
      withTraceNode `Clap.Compile.consiliumMagnum.pass formatExprIter do

      modifyDbgState (CompilerDbgState.setRunUnfold · false)

      let (e', _) ← withTraceNode `Clap.Compile.consiliumMagnum.pass.structurale formatExprChanged?With do
        consiliumStructurale e

      let (e'', _) ← withTraceNode `Clap.Compile.consiliumMagnum.pass.functionale formatExprChanged?With do
        consiliumFunctionale e'

      let (e''', _) ← withTraceNode `Clap.Compile.consiliumMagnum.pass.generale formatExprChanged?With do
        consiliumGenerale e''

      let (e'''', _) ← withTraceNode `Clap.Compile.consiliumMagnum.pass.explicare formatExprChanged?With do
        consiliumExplicare e'''

      if Sym.isSameExpr e e''''
      then return (e'''', numPasses)
      else
        trace[Clap.Compile.consiliumMagnum] m!"{logRewrite e e'''}"
        ire e''' numPasses.succ

def doNothing : MetaM Sym.Simp.Methods := pure {
  pre := λ _ => pure .rfl
  post := λ _ => pure .rfl
  : Sym.Simp.Methods
}

def desperateGeneral : MetaM Sym.Simp.Methods :=
  -- mkMethods #[(`Clap.Compiler.Sets.Structural.logVisitStructural, .Pre)] >>
  mkMethods #[
    (``Sets.General.range, .Pre),
    (``Sets.General.set, .Pre),
    (``Sets.General.getElem, .Post),
    (``Sets.Structural.evalGround, .Post),
    (``Lean.Meta.Sym.Simp.simpControl, .Post),
    (``Sets.General.mapIdx, .Post),
    (``Sets.General.append, .Post)
  ]

def desperateStructure : MetaM Sym.Simp.Methods :=
  -- mkMethods #[(`Clap.Compiler.Sets.Structural.logVisitStructural, .Pre)] >>
  desperateGeneral >>
  mkMethods #[
    (``Compiler.Vector.unwrap, .Pre),
    (``Sets.Structural.foldlM_stagger, .Pre),
  ]

partial def consiliumDesperatum (e : Expr)
                                (extraPasses: MetaM Sym.Simp.Methods)
                                (dbg : ℕ := 12)
                                : Sym.Simp.SimpM Expr := do
  if dbg == 0 then return e
  match e.bind? with
    | .some (a₁, f₁) =>
      logWarning m!"I TOUCH:\n{e}"
      match a₁.bind? with
      | .none =>
        match a₁.pure? with
        | .none => 
          -- `bind <SIMP> _`
          let a₁ ← simp a₁ (←(extraPasses >> desperateStructure))
          let .lam _ _ body _ := f₁ | unreachable!
          let bind ← Sets.Structural.chainActionsInferType #[a₁, body]
          -- logInfo m!"[bind <simp> _]\n{e}\n==>\n{bind}"
          consiliumDesperatum bind extraPasses dbg.pred
        | .some _ =>
          -- `bind (pure _) _`
          match ←Sets.Structural.pureBindMany e with
          | .rfl .. => throwError m!"Pure bind many must succeed"
          | .step e' .. =>
            let e' ← simp e' (←(extraPasses >> desperateGeneral))
            -- logInfo m!"[bind (pure _) _ + simp]\n{e}\n==>\n{e'}"
            consiliumDesperatum e' extraPasses
      | .some .. =>
        -- `bind (bind _) _`
        match ←Sets.Structural.flattenBindsAny e with
        | .rfl .. => throwError m!"Bind flattener on nested bind must succeed"
        | .step (e' := e') .. =>
          -- logInfo m!"[bind (bind _) _]\n{e}\n==>\n{e'}"
          consiliumDesperatum e' extraPasses dbg.pred
    | _ => return e
    where
      simp (e : Expr) (symset : Sym.Simp.Methods) : Sym.Simp.SimpM Expr := do
        let res ← Sym.simp e symset <&> (·.getResultExpr e)
        return Simp.unwrapped res

def compile (e : Expr) (extraPasses: MetaM Sym.Simp.Methods := doNothing) : Sym.Simp.SimpM Expr := do
  let e ← Compiler.Simp.preprocessExpr e
  let res ← lambdaTelescope e fun args e ↦ do
    -- let (compiled, time) ← Dbg.timeS (consiliumDesperatum e extraPasses)
    let (compiled, time) ← Dbg.timeS (consiliumMagnum e extraPasses)
    trace[Clap.Compile] m!"Compilation took: {time}s."
    Dbg.inDebugOnly (do getDbgState >>= fun σ ↦ do logInfo m!"{←σ.pretty}")
    Sym.mkLambdaFVarsS args compiled
  Sym.shareCommonInc res

end Clap.Compiler
