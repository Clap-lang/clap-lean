import Lean
import Qq

import Lean.Meta.Sym.SymM
import Lean.Meta.Tactic.Cbv.Main

import Clap.Lang
import Clap.Spec
import Clap.Compiler.Constraints
import Clap.Compiler.Simp
import Clap.Compiler.Vectors
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean Meta Qq Elab

/-
Thoughts and prayers:
1. e.g. `#v[a1, a2, ...].mapM f → #v[f a1, f a2, f ...]`
   to   `↓f a1 >>= res ↦ #v[f a2, f ...].mapM f`

2. Top level:
   `a >>= b >>= c`
   `↓a >>=`
      `↓b >>=`
        `↓c`

3. All exprs can be made smaller by sacrificing proofs.
   This needs hand-crafting an alternate `rewrite` function /
   changing every simp lemma to a simproc
-/

instance {m} [Monad m] : Union (m Sym.Simp.Methods) where
  union a b := do return (←a) ∪ (←b)

theorem _root_.List.drop_toArray {α} {l : List α} {i} :
  l.toArray.drop i = (l.drop i).toArray := by
  simp only [
    Array.drop_eq_extract, List.size_toArray, List.extract_toArray,
    List.extract_eq_take_drop, Array.mk.injEq
  ]
  rw [←List.extract_eq_take_drop, List.drop_eq_extract]

/--
YEEEEEHAAAAAAAAW, you rootin' tootin' cowboy.
-/
def cowboyCast (e : Expr) (yourDeepestDesire : ℕ) : Sym.SymM Expr := do
  let t ← Sym.inferType e
  let_expr Vector t sz := t | throwError m!"Not a true cowboy."
  let proof ← mkEq t (←mkAppM ``Vector #[t, mkNatLit yourDeepestDesire]) -- TODO: Nuke mapM
  let e' ← e.rewriteType (←mkSorry proof false)
  logInfo m!"Cowboy cast:\n{e}\n==>\n{e'}"
  return e'

@[inherit_doc Simp.wrapped]
abbrev singlePass := Simp.wrapped

namespace SymSets

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
  return simprocs.foldl (· <|> ·) (fun _ ↦ return .rfl) -- I hope this is the `.continue`...

def andThen (names : Array Name) : MetaM Sym.Simp.Simproc := do
  let simprocs ← names.mapM getSimproc
  return simprocs.foldl (· >> ·) (fun _ ↦ return .rfl) -- I hope this is the `.continue`...

-- dischargeSimpSelf
def mkPostMethods (declNames : Array Name)
                  (d : Discharger := Sym.Simp.dischargeNone) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← andThen procs.toArray
  return { post := (←mkSimprocFor thms.toArray d) >> procs }

/--
I thought this would sigle-pass, but apparently not.
-/
def mkPostMethodsSinglePass (declNames : Array Name)
                            (d : Discharger := Sym.Simp.dischargeSimpSelf) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← orElse procs.toArray
  return { post := procs >> (←mkSimprocFor thms.toArray d) }

-- dischargeSimpSelf
def mkPreMethods (declNames : Array Name)
                 (d : Discharger := Sym.Simp.dischargeNone) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← andThen procs.toArray
  return { pre := procs >> (←mkSimprocFor thms.toArray d) }

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

/--
This is more or less `Lean.Meta.Tactic.Cbv.zetaReduce`, which seems to not be exported.

In `Sym`, maybe we can choose to not `zeta` certain things without breaking `simp`?
-/
private def zetaReduce : Simproc := fun e ↦ do
  let .letE _ _ value body _ := e | return .rfl
  let new := expandLet body #[value]
  let new ← Sym.share new
  trace[Clap.Compile.simp.proc.zeta]
    m!"\n{e}\n==>\n{new}"
  return .step new (←Sym.mkEqRefl new)

/--
This is more or less `Lean.Meta.Tactic.Cbv.betaReduce`, which seems to not be exported.
-/
def betaReduce : Simproc := fun e ↦ do
  let .app e arg := e | return .rfl
  let .lam .. := e | return .rfl
  logInfo m!"e: {e}"
  let e' := e.beta #[arg]
  logInfo m!"e': {e'}"
  return .step (←shareCommonInc e') (←Sym.mkEqRefl e')

def zeta : MetaM Methods := do
  return {
    pre := zetaReduce
  }

def beta : MetaM Methods := do
  return {
    pre := betaReduce
  }

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


def compilerSet_whatever : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc, ``bind_assoc,
    ``Option.pure_def,
    ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
    ``Option.map_eq_map, ``Option.map_some, ``Option.pure_apply
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

private def _root_.Lean.Expr.matchBindsE (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | Bind.bind _ _ _ _ a f => .some (a, f)
  | Option.bind   _ _ a f => .some (a, f)
  | _                     => .none

private def _root_.Lean.Expr.matchBindsEInfo (e : Expr) : Option (List Level × Array Expr) :=
  match_expr e with
  | Bind.bind _ _ α β a f => .some (e.getAppFn.constLevels!, #[α, β, a, f])
  | Option.bind   α β a f => .some (e.getAppFn.constLevels!, #[α, β, a, f])
  | _                     => .none

def bind_eq_bind_sym {α} {β} := (Option.bind_eq_bind (α := α) (β := β)).symm

def compilerBindEqBind : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``bind_eq_bind_sym
  ]

def inDebugOnly (m : Sym.Simp.SimpM Unit) : Sym.Simp.SimpM Unit := do
  if (←getBoolOption ``Clap.traversalDbg) then
    m

def monadBindAssoc : Sym.Simp.Simproc := fun e ↦ do
  match e.matchBindsEInfo with
  | .some (_, #[_, γ, x, g]) =>
    match x.matchBindsEInfo with
    | .some (_, #[α, β, x, f]) =>
      -- let subtree := (←Sym.simp f).getResultExpr f
      -- trace[Clap.Compile.simp.proc.monad.bind_assoc]
      --   m!"Subtree.\n{f}\n==>\n{subtree}"
      let u ← Sym.getLevelInType α
      let v ← Sym.getLevelInType β
      let w ← Sym.getLevelInType γ
      -- `f : α → m β | g : β → m γ | x : m α`
      let bind ← shareCommonInc <|
        mkApp4 (.const ``Option.bind [v, w]) β γ (←shareCommonInc (f.beta #[.bvar 0])) g
      let cont := Expr.lam `_assoc α bind .default
      let e' ← shareCommonInc <| mkApp4 (.const ``Option.bind [u, w]) α γ x cont
      inDebugOnly (do
        recordDbgHisto x
      )
      trace[Clap.Compile.simp.proc.monad.bind_assoc]
        m!"INLINED: {x}\n{(←Sym.simp e (←compilerBindEqBind)).getResultExpr e}\n==>\n{(←Sym.simp e' (←compilerBindEqBind)).getResultExpr e'}"
      return .step e' (←mkSorry (←mkEq e e') false)
    | _ =>
      return .rfl
  | _ => return .rfl

def monadBindAssocSimple : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``Option.bind_assoc
  ]

def monads : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``monad,
  ]

def compilerAssoc : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``monadBindAssoc
  ]

def compilerAssocPost : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``monadBindAssoc
  ]

end General

namespace Vector

-- -- Essentially `Vector.mk_append_mk`.
-- -- currently unused, TODO nuke mkAppM
-- private def mk_append_mk' : Simproc := fun e ↦ do
--   let_expr HAppend.hAppend _ _ _ _ xs ys := e | return .rfl
--   let_expr Vector t szXs := ←Sym.inferType xs | return .rfl
--   let_expr Vector _ szYs := ←Sym.inferType ys | return .rfl
--   let_expr Vector.mk _ _ xs _ := xs | return .rfl
--   let_expr Vector.mk _ _ ys _ := ys | return .rfl
--   match szXs.nat?, szYs.nat? with
--   | .some szXs, .some szYs =>
--     -- The trick here is to enforce _syntactically_ that `szXs + szYs` for concrete values
--     -- is evaluated. `Vector.mk_append_mk` leaves `q(szXs + szYs)`.
--     let append ← mkAppM ``HAppend.hAppend #[xs, ys]
--     let szAppend := toExpr (szXs + szYs)
--     let szAppendProof ← mkSorry (←mkEq (←mkAppM ``Array.size #[append]) szAppend) false
--     let e' := mkAppN
--                 (.const ``Vector.mk [←getDecLevel t])
--                 #[t, szAppend, append, szAppendProof]
--     let e' ← Compiler.Simp.reducedAndSharedInc e'
--     -- let e' ← Sym.shareCommonInc e'
--     let proof ← mkSorry (←mkEq e e') false -- Probably just `Vector.mk_append_mk` up to defeq
--     trace[Clap.Compile.simp.proc.mk_append_mk]
--       m!"\n{e}\n==>\n{e'}"
--     return .step e' proof
--   | _ , _ =>
--     -- TODO: I have a feeling this sometimes misbehaves for some reason, look into this.
--     -- Notably, when using `Vector.getElem_mk` 'directly', it simps more things than this guy?
--     -- TODO: Sharing
--     -- logWarning m!"{e} is an append of non-ground size (TODO: remove)"
--     let thm ← mkTheoremFromDecl ``Vector.getElem_mk
--     thm.rewrite e

/--
We're already doing O(n) work here anyway, maybe yield the length as well.
-/
partial def listElemsOfExpr (e : Expr) (res : Array Expr := #[]) : Option (Array Expr) :=
  match_expr e with
  | List.cons _ hd tl => listElemsOfExpr tl (res.push hd)
  | List.nil  _       => .some res
  | _                 => .none

def arrayElemsOfExpr (e : Expr) : Option (Array Expr) := do
  let_expr Array.mk _ l := e | .none
  listElemsOfExpr l

def vectorElemsOfMk (e : Expr) : Option (Array Expr × Expr × Expr) := do
  let_expr Vector.mk t sz arr _ := e | .none
  return (←arrayElemsOfExpr arr, t, sz)

/--
TODO: Maybe generalise this to `GetElem` supporting collections, but it's not relevant
for the current project.
-/
inductive CollectionKind where | Vector | Array | List
  deriving Repr

structure CollectionType where
  private _mk ::
  t  : Expr
  k  : CollectionKind
  sz : Option Expr
  deriving Repr

def CollectionType.cast (c : CollectionType) (t : CollectionKind) : Option CollectionType :=
  match t with
  | .Vector => if c.sz.isNone then .none else go c t
  | _       => go c t
  where go (c : CollectionType) (k : CollectionKind) : CollectionType := {c with k := k}

def CollectionType.setSize (c : CollectionType) (sz : Expr) : CollectionType :=
  {c with sz := .some sz}

def CollectionType.mkList (elem : Expr) := CollectionType._mk elem .List .none

def CollectionType.mkArray (elem : Expr) := CollectionType.mkList elem |>.cast .Array

def CollectionType.mkVec (elem : Expr) (sz : Expr) :=
  CollectionType.mkList elem |>.setSize sz |>.cast .Vector

structure Collection where
  type     : CollectionType
  listExpr : Expr
  deriving Repr

def Collection.setSize (coll : Collection) (sz : Expr) : Collection :=
  {coll with type := coll.type.setSize sz}

/--
We're already doing O(n) work in `listElemsOfExpr` anyway, maybe yield the goodies as well.
-/
partial def elemsOfListExpr (e : Expr) (elems : Array Expr := #[]) (sz : ℕ := 0) : Array Expr × ℕ :=
  match_expr e with
  | List.cons _ hd tl => elemsOfListExpr tl (elems.push hd) sz.succ
  | _                 => (elems, sz) -- `List.nil` and `_`

def Collection.elems (c : Collection) : Array Expr × Collection :=
  let (elems, sz) := elemsOfListExpr c.listExpr
  ⟨elems, c.setSize (toExpr sz)⟩

def Collection.toExpr (c : Collection) : Sym.Simp.SimpM Expr := do
  match c.type.k with
  | .List => return c.listExpr
  | .Array => shareCommonInc <| mkAppN (.const ``Array.mk [←Sym.getLevelInType c.type.t])
                                       #[c.type.t, c.listExpr]
  | .Vector => shareCommonInc (←mkVecLit c.type.t c.listExpr (←c.type.sz.getDM (unreachable!)))

def Collection.ofExpr (e : Expr) : Option Collection :=
  match_expr e with
  | Vector.mk t sz xs _ => do return ⟨←CollectionType.mkVec t sz, ←listExprOfArrayExpr xs⟩
  | Array.mk  t    _    => do return ⟨←CollectionType.mkArray t, ←listExprOfArrayExpr e⟩
  | List.cons t    _  _ => do return ⟨←CollectionType.mkList t, e⟩
  | List.nil  t         => do return ⟨←CollectionType.mkList t, e⟩
  | _                   => .none
  where
    listExprOfArrayExpr (e : Expr) : Option Expr := do
      let_expr Array.mk _ l := e | .none
      .some l

def Collection.cast (coll : Collection) (t : CollectionKind) : Option Collection := do
  return {coll with type := ←coll.type.cast t}

-- /--
-- Currently separate from the `vectorElemsOfMk` chain.
-- -/
-- def elemsOfColl (e : Expr) : Option (Collection × Array Expr × Expr) :=
--   match_expr e with
--   | Vector.mk t sz _ _ => (.Vector t sz, ·) <$> (vectorElemsOfMk e)
--   | Array.mk t _      => arrayElemsOfExpr' e >>= fun res ↦ .some (.Array t, spoon res)
--   | _                 => listElemsOfExpr' e >>= fun res ↦ .some (.List, spoon res)
--   where spoon := fun (arr, t, sz) ↦ (arr, t, toExpr sz)

def Collection.elemsOfExpr (e : Expr) : Option (Array Expr × Collection) :=
  Collection.elems <$> Collection.ofExpr e

def _root_.Lean.Expr.listLitTail (e : Expr) : Option Expr :=
  match_expr e with
  | List.cons _ _ tl => .some tl
  | _ => .none

def mk_append_mk : Simproc := fun e ↦ do
  let_expr HAppend.hAppend _ _ _ _ xs ys := e | return .rfl

  let .some ⟨xsElems, xs⟩ := Collection.elemsOfExpr xs | return .rfl
  let .some ⟨ysElems, ys⟩ := Collection.elemsOfExpr ys | return .rfl

  let append := xsElems.append ysElems

  -- `xs.type.t = ys.type.t` ∧ `xs.type.k = ys.type.k`
  let .some appendListColl := Collection.ofExpr (←Sym.mkListLit xs.type.t append.toList) | unreachable!
  let instAdd := Expr.const ``instAddNat []
  let inst ← shareCommonInc <| mkApp2 (.const ``instHAdd [0]) q(ℕ) instAdd
  let .some szXs := xs.type.sz | unreachable!
  let .some szYs := ys.type.sz | unreachable!
  let sz := mkApp6 (.const ``HAdd.hAdd [0, 0, 0]) q(ℕ) q(ℕ) q(ℕ) inst szXs szYs
  let .some appendVecColl := appendListColl.setSize sz |>.cast xs.type.k | unreachable!
  let e' ← appendVecColl.toExpr

  trace[Clap.Compile.simp.proc.vector_mk_append_mk]
    m!"\n{e}\n==>\n{e'}"

  return .step e' (←mkSorry (←mkEq e e') false)

def append : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_append_mk--, ``List.append_toArray,

    -- ``List.cons_append, ``List.nil_append, ``List.append_nil,

    -- ``Compiler.explodeVectorAppend,

    -- ``appendDbg
  ]

def explode : MetaM Methods := do
  return {
    -- post := explodeVector
    pre  := dontExplodeVector >> explodeVector
  }

open Collection in
/--
We permit any free variable of type vector with size we can reduce to ground nat.
Unsized collections better enumerate their elements in the first place.
-/
def sequenced (e : Expr) : Sym.Simp.SimpM (Option (Array Expr × Collection)) := do
  match_expr e with
  | List.cons _ _ _   => return elemsOfExpr e
  | List.nil  _       => return elemsOfExpr e
  | Array.mk  _ _     => return elemsOfExpr e
  | Vector.mk _ _ _ _ => return elemsOfExpr e
  | _ =>
    if !e.isFVar then return .none
    let_expr Vector t sz := ←Sym.inferType e | return .none
    elemsOfExpr <$> sequenceAsVecExpr e t sz

def _root_.Lean.Expr.foldlM? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.foldlM _ β α _ _ f init xs => .some [α, β, f, init, xs]
  | Array.foldlM α β _ _ f init xs _ _ => .some [α, β, f, init, xs]
  | List.foldlM _ _ β α f init xs => .some [α, β, f, init, xs]
  | _ => .none

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

/-
do let x : t₁ ← a1
   a2
   let x ← do a3; a4; return 4
   a3 x
-/ --> [(a1, t₁), (a2, t₂), (a3, t₃), (a4, t₄), (return 4, ℕ), a3]

partial def _root_.Lean.Expr.sequenceBindsL (e : Expr) : Array (Expr × Expr) :=
  go #[e] #[]
where
  go (todo : Array Expr) (done : Array (Expr × Expr)) : Array (Expr × Expr) :=
    match todo.back? with
    | .none => done
    | .some e =>
      let todo := todo.pop
      match e.matchBindsE with
      | .some (action, func) =>
        match action.matchBindsE with
        | .some (b, g) =>
          go (todo.append #[func, g, b]) done
        | _ =>
          go (todo.push func) (done.push (action, default))
      | _ =>
        match e with
        | .lam _ dom body _ =>
          -- TODO cover case of passing a lambda directly into sequenceBindsL
          -- Actually this is fine...
          -- `.lam x q(Nat) q(True) default` yields `(q(True), default)`,
          -- which is the 'untyped' last action of a sequence.
          let done := done.modify done.size.pred fun (a, _) ↦ (a, dom)
          go (todo.push body) done
        | _ =>
          go todo (done.push (e, default))

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

/--
We pass along the types instead of inferring them from expressions. I guess that's faster :).
TODO: Should also grab universes...
-/
def bindActions (a₁ a₁type a₂ a₂type: Expr) : Sym.Simp.SimpM (Expr × Expr) := do
  let cont := Expr.lam `a a₁type a₂ default
  let bind :=
    mkApp4 (.const ``Option.bind [←Sym.getLevelInType a₁type, ←Sym.getLevelInType a₂type])
           a₁type a₂type
           a₁
           cont
  return (bind, a₂type)

def chainActions (t : Expr) (actions : Array (Expr × Expr)) : Sym.Simp.SimpM Expr := do
  let .some (action, _) := actions.back? | throwError m!"expected some action"
  let actions := actions.pop
  let (e', _) ← actions.foldrM (init := (action, t)) fun (a₁, ta₁) (a₂, ta₂) ↦
    bindActions a₁ ta₁ a₂ ta₂
  let e' ← Sym.shareCommon e'
  return e'

-- (bind (bind (b : Option α) (g : α → Option β) : Option β) (f : β → Option γ) : Option γ)
-- TODO: use `chainActions`
def bindMyAssoc : Sym.Simp.Simproc := fun e ↦ do
  let_expr Option.bind β γ a f := e | return .rfl
  let_expr Option.bind α β b g := a | return .rfl
  let actions := a.sequenceBinds
  if actions.isEmpty then throwError m!"empty nested do block"
  let actions := actions.modify actions.size.pred fun (e, _) ↦ (e, γ)
  let .lam _ _ body _ := f | throwError m!"expected lambda"
  let (e', _) ← actions.foldrM (init := (body, γ)) fun (a₁, ta₁) (a₂, ta₂) ↦
    bindActions a₁ ta₁ a₂ ta₂
  -- let (e', time) ← timeS (Sym.shareCommon e')
  -- logInfo m!"sharing took: {time}s"
  let e ← Sym.shareCommon e'
  return .step e' (←mkSorry (←mkEq e e') false)

def bindMyAssoc_set : MetaM Methods :=
  mkPostMethods #[
    ``bindMyAssoc
  ]

def monads! : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``SymSets.General.monad, ``bindMyAssoc
  ]

opaque eq0 (n : Nat) : Option Unit

-- circuit (vec : Vector 2 Nat)...
-- let x : List Nat := f x

/--
This is for the custom traversal.

TODO(untested, perf, needs restructuring)
-/
def foldlM_singlePass : Sym.Simp.Simproc := fun e ↦ do
  let .some [α, β, f, init, xs] := e.foldlM? | return .rfl
  /-
  TODO(perf): With head|tail reasoning, we don't need to traverse the full list literal expr.
              Using `sequenced` does just that.
  -/
  let .some (elems, ⟨⟨_, k, .some sz⟩, listExpr⟩) ← sequenced xs | return .rfl
  let szSimped := (←Sym.simpWithGround sz).getResultExpr sz
  match szSimped.nat? with
  | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e} (TODO: Maybe this is ok.)"
  | .some _szSimpedNat => -- TODO(check)
    let u ← Sym.getLevelInType β
    let v ← Sym.getLevelInType α
    let w := u -- `Option : Type u ↦ Type u` preserves the universe
    match elems with
    | ⟨[]⟩ =>
      let e' ← Sym.shareCommonInc <| mkAppN (.const ``Option.some [u]) #[β, init]
      return .step e' (←mkSorry (←mkEq e e') false) (done := true)
    | ⟨.cons x _xs⟩ =>
      -- `f init x`
      let head ← Sym.shareCommonInc <| mkApp2 f init x
      -- `_xs` but as list literal
      let .some xs := listExpr.listLitTail | unreachable!
      -- TODO(check): I _think_ I got the universes right.
      -- `List.foldlM f acc xs` where `acc` comes from the enclosing bind
      let tail ← Sym.shareCommonInc <| mkApp3 (.const ``List.foldlM [u, w, v]) f (.bvar 0) xs
      -- `bind head tail`
      let bind ← Sym.shareCommonInc <| mkApp2 (.const ``Option.bind [v, u]) head tail
      return .step bind (←mkSorry (←mkEq e bind) false) (done := true)

def foldlM : MetaM Methods :=
  mkPreMethods #[
    ``Vector.foldlM_mk, ``List.foldlM_toArray,

    ``List.foldlM_cons, ``List.foldlM_nil
  ]

def foldlM_singlePass_s : MetaM Methods :=
  mkPreMethods #[
    ``foldlM_singlePass
  ]

def foldlM_post : MetaM Methods :=
  mkPostMethods #[
    ``Vector.foldlM_mk, ``List.foldlM_toArray,

    ``List.foldlM_cons, ``List.foldlM_nil
  ]

def getElem_mk : Sym.Simp.Simproc := fun e => do
  -- In vector, we can optimise by not enumerating all elements first,
  -- and then taking the size of the final list.

  -- Instead, we can simply traverse the first `i` conses, as we have the length apriori for the proof.
  -- Or some such.
  let_expr GetElem.getElem _ _ _ _ _ vec n _ := e | return .rfl
  let .some (elems, t) := Collection.elemsOfExpr vec | return .rfl
  let .some sz := t.type.sz | unreachable!
  let n := (←Sym.simpWithGround n).getResultExpr n
  let .some i := Sym.getNatValue? n | return .rfl
  if h : i < elems.size
  then
    let e' := elems[i]
    trace[Clap.Compile.simp.proc.vector_getElem_mk]
      m!"\n{e}\n==>\n{e'}"
    return .step e' (←Sym.mkEqRefl e')
  else
    return .rfl

open SymSets

def toArray : MetaM Methods :=
  mkPostMethods #[
    ``Vector.toArray_mk
  ]

def getElem : MetaM Methods :=
  mkPostMethods #[
    ``getElem_mk
  ]

def getElem_old : MetaM Methods :=
  mkPostMethods #[
    ``Vector.getElem_mk, ``List.getElem_toArray,

    ``List.getElem_cons_zero, ``List.getElem_cons_succ,
  ]

def map : MetaM Methods :=
  mkPostMethods #[
    ``Vector.map_mk, ``List.map_toArray,

    ``List.map_cons, ``List.map_nil,
  ] ∪ mapOptim
  where
    mapOptim : MetaM Methods := mkPreMethods #[``List.map_id]

def mapIdx_mk : Sym.Simp.Simproc := fun e => do
  let_expr Vector.mapIdx _ β sz f xs := e | return .rfl
  let some (xs, _) := vectorElemsOfMk xs | return .rfl

  let result ← Sym.mkListLit β (xs.mapIdx (f.beta #[mkNatLit ·, ·])).toList
  let e' ← mkVecLit β result sz

  trace[Clap.Compile.simp.proc.vector_mapIdx_mk]
    m!"\n{e}\n==>\n{e'}"

  return .step e' (←mkSorry (←mkEq e e') false)

def mapIdx : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapIdx_mk
  ] ∪ SymSets.General.ground

def listOfArray (e : Expr) : Option Expr :=
  if e.isAppOf ``List.toArray || e.isAppOf ``Array.mk
  then .none
  else .some e.getAppArgs[1]!

def mapM? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.mapM _ α β _ _ f xs => .some [f, α, β, xs]
  | Array.mapM α β _ _ f xs    => .some [f, α, β, xs]
  | List.mapM _ _ α β f xs     => .some [f, α, β, xs]
  | _                          => .none

open Compiler.Simp in
/--
Single step transformation. TODO: Does not play particularly nice with our top-level driver.
`Vector.mapM f #v[x₀, x₁, ..., xₘ]` ==>
`f x₀ >>= fun row₀ ↦ f x₁ >>= fun row₁ ↦ ... fun rowₘ ↦ .some #v[row₀, row₁, ..., rowₘ]`
-/
def _root_.Vector.mapM_mk : Sym.Simp.Simproc := fun e ↦ do
  let .some [f, _, β, xs] := mapM? e | return .rfl
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

open Compiler.Simp in
/--
Single step transformation. TODO: Does not play particularly nice with our top-level driver.
`Vector.mapM f #v[x₀, x₁, ..., xₘ]` ==>
`f x₀ >>= fun row₀ ↦ f x₁ >>= fun row₁ ↦ ... fun rowₘ ↦ .some #v[row₀, row₁, ..., rowₘ]`
-/
def _root_.Vector.mapM_mk_seq : Sym.Simp.Simproc := fun e ↦ do
  let .some [f, _, β, xs] := mapM? e | return .rfl
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
    trace[Clap.Compile.simp.proc.vector_mapM_mk]
      m!"SEQ: {e'.sequenceBindsL}"
    return .step e' proof

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
  -- reportMaxShared e (descr := "BEGIN[mapM_mk_single]")
  let l ← arr.getAppArgs[1]?.getDM (unreachable!)
  let u ← Sym.getLevelInType β
  let_expr List.cons t hd tl := l |
    -- `#v[].mapM f ==> pure #v[]`
    let e' := mkApp2 (.const ``Option.some [u]) β (←mkVecLit β (←Sym.mkListLit β []) q(0))
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

def mapM_seq : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk_seq
  ]

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
  ] ∪ drop ∪ take ∪ SymSets.General.ground


def size : MetaM Methods :=
  mkPostMethods #[
   ``Vector.size_toArray, ``List.size_toArray,

   ``List.length_cons, ``List.length_nil
  ]

def foldr : MetaM Methods :=
  mkPostMethods #[
    ``Vector.foldr_mk, ``List.foldr_toArray', ``List.foldr_toArray,

    ``List.foldr_cons, ``List.foldr_nil,

    -- ``Compiler.explodeVectorFoldr
  ] ∪ size ∪ SymSets.General.ground

def sum : MetaM Methods :=
  mkPostMethods #[
    ``Vector.sum_eq_foldr
  ] ∪ foldr

def set_mk : Sym.Simp.Simproc := fun e => do
  let_expr Vector.set t sz xs i x h := e | return .rfl
  let some (xs, _, _) := vectorElemsOfMk xs | return .rfl
  let iGround := (←simpWithGround i).getResultExpr i
  match Sym.getNatValue? iGround with
  | .none => throwError m!"Not ground: {iGround}. Request:\n{e}"
  | .some iNat =>
    -- TODO: I guess we can `Vector.set` with `h`.
    let result ← Sym.mkListLit t (xs.set! iNat x).toList
    let e' ← mkVecLit t result sz
    trace[Clap.Compile.simp.proc.vector_set_mk]
      m!"\n{e}\n==>\n{e'}"
    return .step e' (←mkSorry (←mkEq e e') false)

def set : MetaM Methods :=
  mkPostMethods #[
    ``Vector.set_mk
    -- ``List.set_toArray,

    -- ``List.set_cons_succ, ``List.set_cons_zero,
  ]

def processWrapped : Sym.Simp.Simproc := fun e ↦ do
  let_expr Simp.clapwrap _ e := e | return .rfl
  return .rfl (done := true)

def wrapped : MetaM Methods :=
  mkPreMethods #[``processWrapped]

end Vector

namespace List

def reduceRange : Sym.Simp.Simproc := fun e ↦ do
  let_expr _root_.List.range k ← e | return .rfl
  match (←Sym.simp k).getResultExpr k |>.nat? with
  | .none => logError m!"{(←Sym.simp k).getResultExpr k} is not ground"
             return .rfl -- (done := true)
  | .some n => let l := _root_.List.range n
               let e' ← Sym.shareCommonInc (Lean.toExpr l)
              --  let e' ← Simp.reducedAndSharedInc (Lean.toExpr l)
               return .step e' (←mkSorry (←mkEq e e') false) -- This is just rfl.

def range : MetaM Methods := do
  return {
    post := reduceRange
  }

end List

end

end SymSets

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

def logOfExprs (e e' : Expr) : MessageData :=
  m!"\n{e}\n==>\n{e'}"

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

mutual

private partial def down (reduce reduceOuter : Simplifier)
                         (stack : List InProgressExpr) (todo : Expr)
                         : Sym.Simp.SimpM Expr := do
  inDebugOnly (do modifyDbgState fun σ ↦ {σ with numDown := σ.numDown + 1})
  -- See the docs of `unwrapped`
  -- let todo := unwrapped todo
  let .some ⟨_, _, _, β, _, _⟩ ← todo.matchBinds | return todo
  let binds := todo.sequenceBindsL
  logInfo m!"e: {todo}\nbinds:"
  let simpedBinds ← binds.mapM fun (action, τ) ↦ do
    let (simped, time) ← Dbg.timeS (reduce action)
    trace[Clap.Compile.down] logOfExprs action simped
    inDebugOnly do trace[Clap.Compile.dbg] m!"simp took {time}s"
    return (simped, τ)
  let binds := SymSets.Vector.chainActions β simpedBinds
  logInfo m!"binds: {←binds}"
  binds

  -- if let .some ⟨_, _, _, _, a, f⟩ ← todo.matchBinds -- TODO(perf): Propagate the rest.
  -- then
  --   trace[Clap.Compile.down] m!"\npush [→]:\n{f}\ngo [↓]:\n{a}"
  --   down reduce reduceOuter (.inr f :: stack) a
  -- else
  --   let (simped, time) ← Dbg.timeS (reduce todo)
  --   inDebugOnly (do
  --     trace[Clap.Compile.dbg] m!"simp [↓] took {time}s"
  --     modifyDbgState fun σ ↦ {σ with cumulativeSimpTimeDown := σ.cumulativeSimpTimeDown + time}
  --   )
  --   if !Sym.isSameExpr simped todo
  --   then
  --     trace[Clap.Compile.simp] "[↓] {checkEmoji}\n{todo}\n==>\n{simped}"
  --     trace[Clap.Compile.down] "\ngo [↓]:\n{simped}"
  --     down reduce reduceOuter stack simped
  --   else
  --     trace[Clap.Compile.simp.fail] "[↓] {crossEmoji}\n{todo}"
  --     trace[Clap.Compile.down] "\ngo [↑]:\n{todo}"
  --     -- match ←isGroundTerm todo with
  --     -- | .some e => trace[Clap.Compile.simp.warnDownNotGround] "{stopEmoji} [↓] stopped:\n{e}"
  --     -- | .none => pure ()
  --     up reduce reduceOuter stack todo

private partial def up (reduce reduceOuter : Simplifier)
                       (stack : List InProgressExpr) (done : Expr) : Sym.Simp.SimpM Expr := do
  inDebugOnly (modifyDbgState fun σ ↦ {σ with numUp := σ.numUp + 1})
  match stack with
  | [] =>
    trace[Clap.Compile.up] "Done"
    return done
  | .inr e :: stack => do
    -- TODO: Bad idea to use the One! guy, need to eta-expand if need be if so...
    lambdaTelescope e fun arg body ↦ do
      let #[arg] := arg | unreachable!
      trace[Clap.Compile.up] "\npush [←]:\n{(done, arg)}\ngo [↓]:\n{body}"
      down reduce reduceOuter (.inl {action := done, result := arg} :: stack) body
  | .inl ⟨a, result⟩ :: stack => do
    let bind ← mkBindWith a result done
    let up := up reduce reduceOuter stack
    let lamArgT ← Sym.inferType result -- TODO(perf): Propagate universe/type info from `matchBinds`.
    if lamArgT.isUnital
    then trace[Clap.Compile.up] "\ngo [↑]:\n{bind}"
         up bind
    else trace[Clap.Compile.simp] "Binding value: {result} in {bind}"
         let (simped, time) ← Dbg.timeS (reduceOuter bind)
        --  let (simped, time) := (bind, 0)
         inDebugOnly (do
           trace[Clap.Compile.dbg] m!"simp [↑] took {time}s"
           trace[Clap.Compile.dbg] m!"\n{bind}\n==>\n{simped}"
           modifyDbgState fun σ ↦ {σ with cumulativeSimpTimeUp := σ.cumulativeSimpTimeUp + time}
         )
         -- TODO(semantics): Ok we simped, so what?
         if !Sym.isSameExpr simped bind
         then trace[Clap.Compile.simp] "[↑] {checkEmoji}\n{bind}\n==>\n{simped}"
         else trace[Clap.Compile.simp.fail] "[↑] {crossEmoji}\n{bind}"
         trace[Clap.Compile.up] "\ngo [↑]:\n{simped}"
         up simped
  where mkBindWith (a result k : Expr) : Sym.Simp.SimpM Expr := do
    -- TODO(perf): Propagate universe/type info from `matchBinds`.
    -- logInfo m!"a: {a}\nresult: {result}\nk: {k}"
    let α ← result.fvarId!.getType
    let u ← Sym.getLevelInType α
    let β ← Sym.inferType k
    let_expr Option t' := β | throwError m!"Body return not in `Option. Shouldn't be happening."
    let v ← Sym.getLevelInType t'
    let f ← Sym.shareCommonInc (←Sym.mkLambdaFVarsS #[result] k)
    Sym.shareCommonInc <| mkApp4 (.const ``Option.bind [u, v]) α β a f

end

def compile (e : Expr) (simpset : Sym.Simp.Methods := default) : Sym.Simp.SimpM Expr := do
  let simpset! ← SymSets.Vector.monads! ∪ return simpset
  let e ← Compiler.Simp.preprocessExpr e
  lambdaTelescope e fun args e ↦ do
    let compiled ← down
      (reduce      := Compiler.Simp.simplify simpset!)
      (reduceOuter := Compiler.Simp.simplify simpset!)
      -- (reduceOuter := Compiler.Simp.simplify simpset)
      (stack       := [])
      (todo        := e)
    inDebugOnly do trace[Clap.Compile.dbg] m!"σ: {repr (←getDbgState)}"
    Sym.shareCommonInc (←mkLambdaFVars args compiled)

def compileExample (ex : Name) (simpset : Sym.Simp.Methods := default) (args : Array Expr := #[]) : Sym.Simp.SimpM Expr := do
  -- withTraceNode `Clap.Compile.simp.proc (fun e ↦ return m!"") do
  let e := ((←getEnv).find? ex).get!.value!.beta args
  compile e simpset

def compileJustSym (e : Expr) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Expr := do
  Sym.shareCommonInc (←lambdaTelescope e fun args e ↦ do
    -- let time ← IO.monoMsNow
    let compiled ← Compiler.Simp.simplify (simpset) e -- ∪ (←SymSets.General.compilerSet)) e
    -- logInfo m!"Compiled:\n{compiled}"
    -- Dbg.timeSince time "Compilation took:"
    Sym.mkLambdaFVarsS args compiled) -- >>= (liftM ∘ PrettyPrinter.ppExpr)
    -- [k, m + 12, m]
    -- [k, m,]

def compileExampleJustSym (ex : Name) (simpset : Sym.Simp.Methods) (args : Array Expr := #[]) : Sym.Simp.SimpM Expr := do
  -- withTraceNode `Clap.Compile.simp.proc (fun e ↦ return m!"") do
  let e := ((←getEnv).find? ex).get!.value!.beta args
  compileJustSym e simpset

open SymSets in
elab "compile_just_sym" "[" simps:ident,* "]" : tactic => do
  let simps ← simps.getElems.mapM fun s ↦ realizeGlobalConstNoOverload s.raw
  let methods ← simps.mapM (liftM ∘ Simp.API.getMethodsM)
  let methods ← liftM <| methods.foldl (fun method acc ↦ method ∪ acc) (pure {})
  Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    let time ← IO.monoMsNow
    let res ← (← Sym.simpGoal mvarId methods).toOption
    logInfo m!"compile_just_sym took {Dbg.timeInSecondsOfMs time (←IO.monoMsNow)}s"
    return res

def reportAttempt : Sym.Simp.Simproc := fun e ↦ do
  discard bump
  return .rfl

def rewriteReport : Sym.Simp.Simproc := fun e ↦ do
  let stuff ← Sym.Simp.mkTheoremFromDecl `Clap.Compiler.ExampruSym.a
  let res ← stuff.rewrite e
  match res with
  | .rfl .. => return res
  | .step .. =>
    logInfo m!"Did the rewrite"
    return res

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  resetCounter
  -- let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeNone
  -- let methods : Sym.Simp.Methods := {
  --   pre  := fun _ ↦ return .rfl
  --   post := reportAttempt >> rewriteReport
  -- }
  let methods : Sym.Simp.Methods := {
    pre  := fun _ ↦ return .rfl
    post := reportAttempt >> Clap.Compiler.SymSets.General.betaReduce >> rewriteReport
  }
  Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    let time ← IO.monoMsNow
    let res ← (← Sym.simpGoal mvarId methods).toOption
    logInfo m!"sym_simp took {Dbg.timeInSecondsOfMs time (←IO.monoMsNow)}s"
    logInfo m!"this many times: {←getCounter}"
    return res

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

-- example : tt = tt' := by
--   unfold tt
--   compile_just_sym [SymSets.Vector.bindMyAssoc_set]
--   simp only [←Option.bind_eq_bind]
--   simp only [bind_assoc]
--   unfold tt'

--   rw [Option.bind_assoc]
--   rw [Option.bind_assoc]
--   rw [Option.bind_some]
--   rw [Option.bind_some]
--   rw [Option.bind_some]
--   rw [Option.bind_some]
--   rw [Option.bind_some]
--   rw [Option.bind_some]
--   rfl
--   -- compile_just_sym [SymSets.Vector.bindMyAssoc_set]

def ppMonad (e : Expr) : MetaM Expr := do
  let pretty ← Sym.simp e (←Clap.Compiler.SymSets.General.compilerBindEqBind) |>.run
  return pretty.getResultExpr e

/-- a.k.a tablespoon -/
def liftExpr (m : Sym.Simp.SimpM Expr) : MetaM Expr := do
  m.run' {} |>.run

def spoon (m : Sym.Simp.SimpM Expr) : MetaM Unit := do
  let compiled ← liftExpr m
  let pretty ← ppMonad compiled
  -- logInfo m!"Compiled:\n{compiled}"
  logInfo m!"Compiled:\n{pretty}"


  -- -- (m.run' {} |>.run) >>= PrettyPrinter.ppExpr

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

-- def f := fun x : Nat => (x, fun x₁ : Nat => (x₁, fun x₂ : Nat => x₂))

-- -- `def f := fun x : Nat ↦ fun y : Nat ↦ ...`
-- #check Sym.AlphaKey
-- def inst : Hashable Nat := ⟨fun _ ↦ 0⟩
-- #check Prod.mk
-- def abc : Sym.Simp.SimpM Unit := do
--   -- let m : @Std.HashMap Nat Nat inferInstance inst :=
--   --   @Std.HashMap.ofArray _ _ _ inst #[(0, 1), (1, 2), (2, 3)]
--   -- for (k, v) in m do
--   --   logInfo m!"{k} → {v}"
--   let env ← getEnv
--   let .some stuff := env.find? ``Clap.Compiler.f | unreachable!
--   let val := stuff.value!
--   let σ ← get
--   let σ := σ.transientCache
--   for (k, v) in σ do
--     logInfo m!"{k.expr} → {v.getResultExpr default}"
--   return ()

-- #eval abc.run' {} |>.run

-- #exit
  -- let σshare₁ := σ.share
  -- for key in σshare₁.set do
  --   logInfo m!"{key.expr}"
  -- logInfo m!"______________________"
  -- let impl ← Sym.shareCommon val
  -- logInfo m!"impl: {impl}"
  -- let σ₂ ← get
  -- let σshare₂ := σ₂.share
  -- let cache₂ := σshare₂.set.toList
  -- let cache₂sorted := cache₂.mergeSort (le := fun e₁ e₂ ↦ e₁.expr.sizeWithoutSharing ≤ e₂.expr.sizeWithoutSharing)
  -- for key in cache₂sorted.zipIdx do
  --   let val := key.1.expr
  --   let_expr Prod.mk _ _ fst snd := val | continue
  --   let res := cache₂sorted.find? fun e ↦ Sym.isSameExpr e.expr snd
  --   logInfo m!"res: {Sym.AlphaKey.expr <$> res}"
  --   if σshare₁.set.contains key.1
  --   then logInfo m!"{checkEmoji}[{key.2}] {key.1.expr}"
  --   else logInfo m!"{crossEmoji}[{key.2}] {key.1.expr}"
  --   logInfo m!"fst: {fst} snd: {snd}"
  -- logInfo m!"first: {σshare₁.set.toList.length}"
  -- logInfo m!"second: {σshare₂.set.toList.length}"
  -- logInfo m!"{←PrettyPrinter.ppExpr (cache₂sorted[28]'sorry).expr}"

-- #eval! abc.run

namespace ExampruSym

namespace NewTraversal
open SymSets Monad General Vector

opaque F : ℕ → Option ℕ
opaque G : ℕ → Option ℕ
opaque H : ℕ → Option ℕ

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


def eq0 (e : Nat) : Option Unit := .some ()

def ex₈ (n : ℕ) (vec : Vector Nat n) : Option Unit := do
  let x ← (do let _ ← eq0 2; let X ← vec.mapM (fun x ↦ (eq0 (x + 42) : Option _)); return 4)
  eq0 x

opaque share : Nat → Option Nat

def ex₉ {n : Nat} (vec : Vector Nat n) : Option Unit := do
  let x ← (do let _ ← eq0 2; let x ← vec.mapM (fun x ↦ (share (x + 42) : Option _)); return x)
  let _ ← x.mapM eq0

set_option maxRecDepth 1024 in
set_option trace.Clap.Compile.dbg true in
set_option Clap.traversalDbg true in
set_option trace.Clap.Compile true in
#eval do
  let (e, time) ← Dbg.timeS <| compileExampleJustSym (args := #[toExpr 3]) ``ex₉
    (←(
      mapM ∪
      getElem ∪
      append ∪
      explode -- ∪ monads -- ∪ zeta ∪ monads ∪ explode
    ∪ compilerAssoc
    -- ∪ bindMyAssoc_set
    ∪ monads
    -- mapM_alt
    )) |>.run' {} |>.run
  logInfo m!"time: {time}"
  -- let e' := Sym.simp e {}
  let e' := Sym.simp e (←compilerBindEqBind)
  let e' ← e'.run

  logInfo m!"e: {e'.getResultExpr e}"
  logInfo m!"{←(getAndResetDbgState <&> repr)}"

opaque A : Nat → Option Nat
opaque B : Nat → Option Nat
opaque C : Nat → Option Nat
opaque D : Nat → Option Nat
opaque E : Nat → Option Nat

def e? (vec : Vector Nat 4) : Option Unit := do
  let _ ← A 1
  let z ← B 2
  let x ← (do let _ ← F 4
              let x ← (do let _ ← C 42; let w ← D z; let _ ← D 42; E (z + w))
              H x)
  F x

def assocPre : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``bind_assoc
  ]

def assocPost : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``bind_assoc
  ]

set_option trace.Clap.Compile.dbg true
set_option Clap.traversalDbg true
set_option trace.Clap.Compile true
#eval do
  let (e, time) ← Dbg.timeS <| compileExampleJustSym ``e?
    (←(
    compilerAssoc
    )) |>.run' {} |>.run
  logInfo m!"time: {time}"
  -- let e' := Sym.simp e {}
  let e' := Sym.simp e (←compilerBindEqBind)
  let e' ← e'.run

  logInfo m!"e: {e'.getResultExpr e}"
  let σ ← getAndResetDbgState
  logInfo m!"{←σ.pretty}"

end NewTraversal

end Clap.Compiler
