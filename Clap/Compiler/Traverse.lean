import Lean
import Qq

import Lean.Meta.Sym.SymM
import Lean.Meta.Tactic.Cbv.Main

import Clap.Lang
import Clap.Spec
import Clap.Compiler.Simp
import Clap.Compiler.Vectors
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean Meta Qq Elab

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

def mkPostMethods (declNames : Array Name)
                  (d : Discharger := Sym.Simp.dischargeSimpSelf) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← andThen procs.toArray
  return { post := (←mkSimprocFor thms.toArray d) >> procs }

def mkPreMethods (declNames : Array Name)
                 (d : Discharger := Sym.Simp.dischargeSimpSelf) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  let procs ← andThen procs.toArray
  return { pre := (←mkSimprocFor thms.toArray d) >> procs }

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
  let new := e.headBeta
  let new ← Sym.share new
  return .step new (←Sym.mkEqRefl new)

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

def compilerWat : Sym.Simp.Simproc := fun e ↦ do
  -- withTraceNode `Clap.Compile.simp.proc.monad (fun _ ↦ return m!"") do
  -- trace[Clap.Compile.simp.proc.monad] m!"{e}"
  match_expr e with
  | Bind.bind _ _ α β x f =>
    -- let time ← IO.monoMsNow
    let u ← Sym.getLevelInType α
    let v ← Sym.getLevelInType β
    let e' ← shareCommonInc <| mkApp4 (.const ``Option.bind [u, v]) α β x f
    trace[Clap.Compile.simp.proc.monad.bind_eq_bind]
      m!"\n{e}\n==>\n{e'}"
    -- Dbg.timeSince time "bind_eq_bind took:"
    return .step e' (←Sym.mkEqRefl e')
  | Pure.pure _ _ α x =>
    -- let time ← IO.monoMsNow
    let u ← Sym.getLevelInType α
    let e' ← shareCommonInc <| mkApp2 (.const ``Option.some [u]) α x
    trace[Clap.Compile.simp.proc.monad.pure_apply]
      m!"\n{e}\n==>\n{e'}"
    -- Dbg.timeSince time "pure_apply took:"
    return .step e' (←Sym.mkEqRefl e')
  | Option.bind α γ x g =>
    match_expr x with
    | Option.bind α β x f => 
      -- let time ← IO.monoMsNow
      let subtree := (←Sym.simp f).getResultExpr f
      trace[Clap.Compile.simp.proc.monad.bind_assoc]
        m!"Subtree.\n{f}\n==>\n{subtree}"
      let u ← Sym.getLevelInType α
      let v ← Sym.getLevelInType β
      let w ← Sym.getLevelInType γ
      -- `f : α → m β | g : β → m γ | x : m α`
      let bind ← shareCommonInc <|
        mkApp4 (.const ``Option.bind [v, w]) β γ (←shareCommonInc (f.beta #[.bvar 0])) g
      let cont := Expr.lam `_assoc α bind .default
      let e' ← shareCommonInc <| mkApp4 (.const ``Option.bind [u, w]) α γ x cont
      trace[Clap.Compile.simp.proc.monad.bind_assoc]
        m!"\n{e}\n==>\n{e'}"
      -- Dbg.timeSince time "bind_assoc took:"
      return .step e' (←mkSorry (←mkEq e e') false)
    | Option.some _ x =>
      -- let time ← IO.monoMsNow
      let e' ← shareCommonInc (g.beta #[x])
      trace[Clap.Compile.simp.proc.monad.bind_some]
        m!"\n{e}\n==>\n{e'}"
      -- Dbg.timeSince time "bind_some took:"
      return .step e' (←Sym.mkEqRefl e')
    | _ =>
      let x' := (←Sym.simp x (←read).toMethods).getResultExpr x
      if isSameExpr x x' then
        trace[Clap.Compile.simp.proc.monad.top_level]
          m!"{checkEmoji} {x'}"
        return .rfl
      -- let f' ← Sym.simp g
      let e' ← shareCommonInc <|
        mkApp4 (.const ``Option.bind [←Sym.getLevelInType α, ←Sym.getLevelInType γ]) α γ x' g
      trace[Clap.Compile.simp.proc.monad.top_level]
        m!"\n{e}\n==>\n{e'}"
      return .step e' (←mkSorry (←mkEq e e') false)
  | _ =>
    return .rfl
  
def compilerWtf : MetaM Sym.Simp.Methods :=
  mkPreMethods #[
    ``compilerWat
  ]

def heh : Sym.Simp.Simproc := fun e ↦ do
  -- logInfo m!"heh: {e}"
  -- let time ← IO.monoMsNow
  match_expr e with
  | Option.bind _ _ a f => 
    let_expr Option.some _ a := a | return .rfl
    let e' ← Sym.shareCommonInc (f.beta #[a])
    return .step e' (←Sym.mkEqRefl e') -- `Option.bind_some`

    -- let thm ← mkTheoremFromDecl ``Option.bind_some
    -- let res ← thm.rewrite e
    -- -- Dbg.timeSince time "heh: "
    -- -- (res.getResultExpr e).checkMaxShared
    -- return res

  | Pure.pure m _ t x =>
    if !m.isConstOf ``Option then return .rfl
    -- let thm ← mkTheoremFromDecl ``Option.pure_apply -- TODO: Probably cache this
    -- let res ← thm.rewrite e
    -- (res.getResultExpr e).checkMaxShared
    -- Dbg.timeSince time "heh: "
    -- return res
    logInfo m!"m: {m}\nt: {t}\nx: {x}"
    let e' ← Sym.shareCommon (mkApp2 (.const ``Option.some [←Sym.getLevelInType t]) t x)
    return .step e' (←Sym.mkEqRefl e')
  | _ => return .rfl

def compilerSetAlt2 : MetaM Sym.Simp.Methods :=
  mkPostMethods (d := Sym.Simp.dischargeNone) #[
    -- ``heh
    -- ``Option.bind_some,
    ``Option.pure_apply
  ]

-- /--
-- TODO: Highly experimental.
-- -/
-- def castGround : Simproc := fun e ↦ do
--   let t ← Sym.inferType e
--   let normalForm ← simpWithGround t
--   if isSameExpr t (normalForm.getResultExpr t)
--   then return .rfl
--   -- TODO: Probably not the best idea.
--   -- We are using `.mp` to detect that a cast has already ocurred, which might not be so smart.
--   if e.isAppOf ``Eq.mp then return .rfl
--   let proof : SymM Expr :=
--     match normalForm with
--     | .rfl .. => Sym.mkEqRefl t
--     | .step _ prf .. => return prf
--   let univ ← Sym.getLevel (normalForm.getResultExpr t)
--   let e' := mkApp4 (.const ``Eq.mp [univ]) t (normalForm.getResultExpr t) (←proof) e
--   trace[Clap.Compile.simp.proc.preprocess]
--     m!"\n{e}\n==>\n{e'}\n\n{t}\n=t=>\n{(normalForm.getResultExpr t)}"
--   return .step e' (←mkSorry (←mkEq e e') false)

-- def cast : MetaM Methods :=
--   mkPostMethods #[
--     ``castGround

--     -- ``appendDbg
--   ]

-- private def seemsTotallySafeInDTT : Simproc := fun e ↦ do
--   let_expr Vector _ n := ←Sym.inferType e | return .rfl
--   let groundSize := (←Sym.simp n (←ground)).getResultExpr n
--   if isSameExpr n groundSize then return .rfl
--   match groundSize.nat? with
--   | .none => throwError m!"{groundSize} is not ground.\nTODO: Maybe this is ok."
--   | .some groundSize =>
--     let cowboyCast e _
--     trace[Clap.Compile.simp.proc.seemsTotallySafeInDTT]
--       m!"{}"
--     return .rfl
--   -- let e' ← Sym.Simp.evalGround {} e
--   -- unless isSameExpr e (e'.getResultExpr e) do
--   --   trace[Clap.Compile.simp.proc.evalGround]
--   --     m!"\n{e}\n==>\n{e'.getResultExpr e}"
--   -- return e'

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

  -- let some (collXs, xs, tXs, szXs) := elemsOfColl xs | return .rfl
  -- let some (collYs, ys, _tYs, szYs) := elemsOfColl ys | return .rfl
  -- -- `tXs = _tYs`
  -- let result ← Sym.mkListLit tXs (xs.append ys).toList

  -- let instAdd := Expr.const ``instAddNat []
  -- let inst ← shareCommonInc <| mkApp2 (.const ``instHAdd [0]) q(ℕ) instAdd

  -- let e' ← liftM ∘ shareCommonInc =<<
  --   mkVecLit tXs result (mkApp6 (.const ``HAdd.hAdd [0, 0, 0]) q(ℕ) q(ℕ) q(ℕ) inst szXs szYs)

  -- trace[Clap.Compile.simp.proc.vector_mk_append_mk]
  --   m!"\n{e}\n==>\n{e'}"
  
  -- return .step e' (←mkSorry (←mkEq e e') false)

def appendDbg : Sym.Simp.Simproc := fun e ↦ do
  let_expr HAppend.hAppend _ _ _ _ xs ys := e | return .rfl
  logInfo m!"DBG:\n{e}"
  let thm ← mkTheoremFromDecl ``Vector.mk_append_mk
  match ←thm.pattern.match? e with
  | .none => logInfo m!"{bombEmoji} Pattern:\n{thm.pattern.pattern}"
  | .some arr => logInfo m!"{checkEmoji} Matched:\n{arr.args}"
  logInfo m!"TRY AGAIN: {(← Sym.unfoldReducible e)}"
  match ←thm.pattern.match? (← Sym.unfoldReducible e) with
  | .none => logInfo m!"{bombEmoji} Pattern:\n{thm.pattern.pattern}"
  | .some arr => logInfo m!"{checkEmoji} Matched:\n{arr.args}"
  return .rfl

def append : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_append_mk--, ``List.append_toArray,

    -- ``List.cons_append, ``List.nil_append, ``List.append_nil,

    -- ``Compiler.explodeVectorAppend,

    -- ``appendDbg
  ]

def explode : MetaM Methods := do
  return {
    post := explodeVector
    pre  := dontExplodeVector
  }

def foldlM : MetaM Methods :=
  mkPostMethods #[
    ``Vector.foldlM_mk, ``List.foldlM_toArray,

    ``List.foldlM_cons, ``List.foldlM_nil
  ]

def getElemDbg : Sym.Simp.Simproc := fun e ↦ do
  logInfo m!"getElemDbg: {e}"
  let_expr GetElem.getElem _ _ _ _ _ coll i h := e | return .rfl
  logInfo m!"coll: {coll}\ni: {i}"
  let_expr Vector.mk _ _ arr h := coll |
    logInfo m!"Rejected: {coll}"
    logInfo m!"App of: {coll.getAppFnArgs}"
    return .rfl
  logInfo m!"arr: {arr}"
  logInfo m!"This is getElem on Vector.mk:\n({coll})[{i}]"
  logInfo m!"e:\n{e}"
  
  let thm ← mkTheoremFromDecl ``Vector.getElem_mk
  logInfo m!"thm pattern: {thm.pattern.pattern}"

  match ← thm.pattern.match? e with
  | .none => logInfo m!"NO MATCH:\n{e}\n=?=\n{thm.pattern.pattern}"
  | .some e' => logInfo m!"YOU TRIGGERED SON! OK!: {e'.args}"

  return .rfl

-- private def getElem_t : Simproc := fun e ↦ do
--   let_expr GetElem.getElem collT _ _ _ _ coll i h := e | return .rfl
--   let_expr Vector _ sz := collT | return .rfl
--   let simpedSz := (←Sym.simp sz (←General.ground)).getResultExpr sz
--   match simpedSz.nat? with
--   | .none => return .rfl
--   | .some simpedSzN =>
--     return .rfl
--     -- if simpedSz == sz then return .rfl -- TODO: `isSameExpr`?
--     -- let coll ← cowboyCast coll simpedSzN
--     -- let e' := ←mkAppM ``GetElem.getElem #[coll, i]
--     -- logInfo m!"e': {e'}"
--     -- -- This plays loose, let's pretend this is ok for now.
--     -- return .step e' (←mkSorry (←mkEq e e') false)
--     -- logInfo m!"szVec: {(←Sym.simp sz (←General.ground)).getResultExpr sz}"
--     -- logInfo m!"szVecSimped: {sz}"
--     -- let_expr Vector.mk _ sz arr _ := coll | return .rfl

--     -- logInfo m!"sz: {sz}"
--     -- logInfo m!"simped sz: {(←Sym.simp sz).getResultExpr sz}"
--     -- return .rfl

-- /--
-- `Vector.getElem_mk` up to reducible.
-- Trying to be as explicit as possible for `Sym`.
-- -/
-- private def getElem_mk : Simproc := fun e ↦ do
--   let_expr GetElem.getElem collT _ _ _ _ coll i h := e | return .rfl
--   let_expr Vector _ _getElemSz := collT | return .rfl
--   let_expr Vector.mk _ _mkSz arr _ := coll | return .rfl
--   -- Note we are not looking at `_getElemSz` and `_mkSz`.
--   logInfo m!"WAT {h}"
--   let szProof ← mkLt i (←mkAppM ``Array.size #[arr])
--   let e' ← mkAppM ``GetElem.getElem #[arr, i, ←mkSorry szProof false]
--   trace[Clap.Compile.simp.proc.getElem_mk] m!"{e}\n==>\n{e'}"
--   return .step e' (←mkSorry (←mkEq e e') false)
--   -- let getElemSz := (←Sym.simp getElemSz (←General.ground)).getResultExpr getElemSz
--   -- let mkSz := (←Sym.simp mkSz (←General.ground)).getResultExpr mkSz
--   -- unless isSameExpr getElemSz mkSz do return .rfl
--   -- trace[Clap.Compile.simp.proc.getElem_mk] m!""
  -- _

-- #check Vector.getElem_mk
-- def getElem_mk : Sym.Simp.Simproc := fun e ↦ do
--   let_expr GetElem.getElem collT _ _ _ _ coll _ _ := e | return .rfl
--   let_expr Vector.mk _ sz arr _ := coll | return .rfl
--   let_expr Vector _ getElemSz := collT | return .rfl
--   logWarning m!"Doing.\nGetElem={getElemSz}\nVec.mk={sz}"
--   if isSameExpr getElemSz sz then -- `1 + 1 ≠ 2`
--     let thm ← mkTheoremFromDecl ``Vector.getElem_mk -- TODO: Don't do this lazily here.
--     let e' ← thm.rewrite e
--     trace[Clap.Compile.simp.proc.vector_getElem_mk]
--       m!"\n{e}\n==>\n{e'.getResultExpr e}"
--     return e'
--   let simpedSz := (←Sym.simp sz (←General.ground)).getResultExpr sz
--   match simpedSz.nat? with
--   | .none =>
--     throwError m!"{simpedSz} is not ground.\nMaybe this is ok."
--     return .rfl
--   | .some simpedSzN =>
--     logInfo m!"sz:{sz}\nsimpedSz: {(←Sym.simp sz (←General.ground)).getResultExpr sz}"
--     let e' ← inferVectorProof (←mkAppM ``GetElem.getElem #[arr, mkNatLit simpedSzN]) -- GetElem (Array Nat)
--     let e' ← Compiler.Simp.reducedAndSharedInc e'
--     trace[Clap.Compile.simp.proc.vector_getElem_mk]
--       m!"\n{e}\n==>\n{e'}\nCheating.\nIn {collT} we pretend that {getElemSz} = {simpedSzN}."
--     return .step e' (←mkSorry (←mkEq e e') false)
-- -- Vector.append : Vec m ++ Vec n ==> Vec (m + n) ==> Vec k where k = n + n
-- -- do let x := (vec ++ vec)[1] -- (vec ++ vec : Vector (m + n)) -- GetElem (Vector (3 + 3)) 
-- #check Vector.append
-- #check GetElem.getElem (coll := Vector ℕ 4) (Vector.mk (n := 2 + 2) #[1, 2, 3, 4] rfl) 0 (by decide)

def getElem_mk : Sym.Simp.Simproc := fun e => do
  -- withTraceNode `Clap.Compile.simp.proc.vector_getElem_mk (fun _ ↦ return m!"") do
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
    -- ``getElem_t,
    ``Vector.getElem_mk, ``List.getElem_toArray,

    ``List.getElem_cons_zero, ``List.getElem_cons_succ,

    -- ``getElemDbg
  ]

def mapDbg : Sym.Simp.Simproc := fun e ↦ do
  let_expr Array.map _ _ _ _ := e | return .rfl
  logInfo m!"Is Array.map:\n{e}"
  let thm ← mkTheoremFromDecl ``List.map_toArray
  match ←thm.pattern.match? e with
  | .none => logInfo m!"{bombEmoji} Pattern:\n{thm.pattern.pattern}"
  | .some e => logInfo m!"{checkEmoji} Pattern:\n{e.args}"
  match ←thm.pattern.match? (←Compiler.Simp.preprocessExpr e) with
  | .none => logInfo m!"{bombEmoji} Pattern:\n{thm.pattern.pattern}"
  | .some e => logInfo m!"{checkEmoji} Pattern:\n{e.args}"
  return .rfl

def map : MetaM Methods :=
  mkPostMethods #[
    ``Vector.map_mk, ``List.map_toArray,
    
    ``List.map_cons, ``List.map_nil,

    -- ``Compiler.explodeVectorMap
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

def mapM? (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Vector.mapM _ α β _ _ f xs => return [f, α, β, xs]
  | Array.mapM α β _ _ f xs    => return [f, α, β, xs]
  | List.mapM _ _ α β f xs     => return [f, α, β, xs]
  | _                          => .none

open Compiler.Simp in
/--
Single step transformation. TODO: Does not play particularly nice with our top-level driver.
`Vector.mapM f #v[x₀, x₁, ..., xₘ]` ==>
`f x₀ >>= fun row₀ ↦ f x₁ >>= fun row₁ ↦ ... fun rowₘ ↦ .some #v[row₀, row₁, ..., rowₘ]`
-/
def _root_.Vector.mapM_mk : Sym.Simp.Simproc := fun e ↦ do
  -- withTraceNode `Clap.Compile.simp.proc.vector_mapM_mk (fun _ ↦ return m!"") do
  -- let time ← IO.monoMsNow
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

/--
`Vector.mapM_mk_singleton_append` is a part of `Vector.mapM_mk_append` to ensure that
the transformation `#v[a, b] ==> #v[a] ++ #v[b]` does not get undone by `Vector.mk_append_mk`.
-/
def mapM : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk

    -- ``Compiler.explodeVectorMapM
  ]

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

def compileJustSym (e : Expr) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Expr := do
  lambdaTelescope e fun args e ↦ do
    -- let time ← IO.monoMsNow
    let compiled ← Compiler.Simp.simplify (simpset) e -- ∪ (←SymSets.General.compilerSet)) e
    -- logInfo m!"Compiled:\n{compiled}"
    -- Dbg.timeSince time "Compilation took:"
    Sym.mkLambdaFVarsS args compiled -- >>= (liftM ∘ PrettyPrinter.ppExpr)

def compileExampleJustSym (ex : Name) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Expr := do
  -- withTraceNode `Clap.Compile.simp.proc (fun e ↦ return m!"") do
  let e := ((←getEnv).find? ex).get!.value!
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

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeNone
  let methods : Sym.Simp.Methods := {
    pre  := fun _ ↦ return .rfl
    post := rewrite
  }
  Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    let time ← IO.monoMsNow
    let res ← (← Sym.simpGoal mvarId methods).toOption
    logInfo m!"sym_simp took {Dbg.timeInSecondsOfMs time (←IO.monoMsNow)}s"
    return res

def eq0 (e : Nat) : Option Unit := .some ()

def spoon (m : Sym.Simp.SimpM Expr) : MetaM Unit := do
  let compiled ← m.run' {} |>.run
  logInfo m!"Compiled:\n{compiled}"
  -- (m.run' {} |>.run) >>= PrettyPrinter.ppExpr

namespace ExampruSym

open SymSets Monad General Vector

-- set_option maxRecDepth 500000
-- set_option trace.Clap.Compile true

def ex₀ : Option Unit := do
  eq0 0
  eq0 1
  let _res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 2)
  eq0 3
  return ()

/--
info: Compiled:
(eq0 0).bind fun x =>
(eq0 1).bind fun x =>
(eq0 2).bind fun y =>
(eq0 2).bind fun _res =>
(eq0 3).bind fun x => some PUnit.unit
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₀ (←(foldlM ∪ compilerSet_old'))

def ex₁ (_vec : Vector Nat 3) : Option Unit := do
  eq0 #v[4, 5][0]
/--
info: Compiled:
fun _vec => eq0 4
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁ (←getElem)

def ex₂ (vec : Vector Nat 160) : Option Unit := do
  let x := (vec ++ vec)[0] -- `GetElem (Vector _ (3 + 3))`
  eq0 x
-- /--
-- info: Compiled:
-- fun vec => eq0 vec[0]
-- -/
-- #guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₂ (←(getElem ∪ append ∪ zeta ∪ explode))

def ex₃ (vec : Vector Nat 200) : Option Unit := do
  let x := vec.map (·+1)
  eq0 x[0]

/--
info: Compiled:
fun vec => eq0 (vec[0] + 1)
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₃ (←(map ∪ zeta ∪ getElem ∪ explode))

def ex₄ (vec : Vector Nat 160) : Option Unit :=
  vec.mapM (fun x ↦ Option.some <| x + 1) |>.bind fun x ↦ eq0 x[0]

-- -- /--
-- -- info: Compiled:
-- -- fun vec => eq0 (vec[0] + 1)
-- -- -/
-- -- #guard_msgs(info, whitespace := lax, drop warning) in
-- set_option pp.exprSizes true in
-- -- set_option trace.Clap.Compile true in
-- set_option trace.Clap.Compile.simp.proc.vector_mapM_mk true in
-- set_option trace.profiler true in
-- set_option profiler true in
-- set_option trace.Clap.Compile true in
set_option trace.Clap.Compile false in
#eval spoon <| do compileExampleJustSym ``ex₄ (←(mapM ∪ compilerWtf ∪ getElem))

def profileThis := spoon <| do compileExampleJustSym ``ex₄ (←(mapM ∪ compilerWtf ∪ getElem))

def ex₅ (vec : Vector Nat 3) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := vec.zipWith (bs := vec.map (·+1)) fun x y ↦ x + y
  eq0 res[0]
  eq0 res[1]
  eq0 res[2]

/--
info: Compiled:
fun vec =>
  (eq0 vec[0]).bind fun x =>
    (eq0 0).bind fun x =>
      (eq0 (vec[0] + (vec[0] + 1))).bind fun x =>
        (eq0 (vec[1] + (vec[1] + 1))).bind fun x => eq0 (vec[2] + (vec[2] + 1))
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do
  compileExampleJustSym
    ``ex₅
    (←(append ∪ explode ∪ getElem ∪ map ∪ zipWith ∪ zeta ∪ compilerSet_old))

def ex₆ (vec : Vector Nat 160) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := (vec.drop 1).take 1
  eq0 res[0]

/--
info: Compiled:
fun vec => (eq0 vec[0]).bind fun x => (eq0 0).bind fun x => eq0 vec[1]
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₆ (←(append ∪ getElem ∪ drop ∪ take ∪ zeta ∪ compilerSet_old ∪ explode))

def ex₇ (vec : Vector Nat 3) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := vec.sum
  eq0 res

/--
info: Compiled:
fun vec =>
(eq0 vec[0]).bind fun x =>
(eq0 0).bind fun x =>
eq0 (vec[0] + (vec[1] + (vec[2] + 0)))
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₇ (←(append ∪ getElem ∪ sum ∪ zeta ∪ compilerSet_old ∪ explode))

def ex₈ (vec : Vector Nat 3) : Option Unit := do
  let vec := vec.zipWith (·+·) #v[1, 5, 10]
  eq0 42
  let res ← vec.mapM (fun n ↦ return n + 1)
  eq0 res[0]
  let y ← (do eq0 4; let y ← pure 4; let z ← #v[1, 2].mapM (return·+42); eq0 z[0]; return y)
  let z := (List.range y)[0]'sorry
  eq0 res[1]
  eq0 res[2]
-- set_option trace.Clap.Compile true in
-- /--
-- info: Compiled:
-- fun vec =>
--   (eq0 42).bind fun x =>
--     (eq0 (vec[0] + 1 + 1)).bind fun x =>
--       (eq0 4).bind fun _assoc =>
--         (eq0 (1 + 42)).bind fun _assoc => (eq0 (vec[1] + 5 + 1)).bind fun x => eq0 (vec[2] + 10 + 1)
-- -/
-- #guard_msgs(info, whitespace := lax, drop warning) in
-- #eval spoon <| do compileExampleJustSym ``ex₈ (←(zipWith ∪ mapM ∪ getElem ∪ zeta ∪ compilerWtf ∪ explode))

def ex₉ (vec : Vector Nat 160) : Option Unit := do
  let res := (#v[0] ++ vec).extract 1 2
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 vec[0]
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₉ (←(extract ∪ append ∪ getElem ∪ zeta ∪ compilerSet_old ∪ explode))

def ex₁₀ (vec : Vector Nat 160) : Option Unit := do
  let res := (#v[0] ++ vec).set 0 42
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 42
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁₀ (←(set ∪ append ∪ getElem ∪ zeta ∪ compilerSet_old ∪ explode))

def ex₁₁ (vec : Vector Nat 160) : Option Unit := do
  let res := vec.mapIdx fun i x ↦ x + i
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 (vec[0] + 0)
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁₁ (←(mapIdx ∪ getElem ∪ zeta ∪ compilerSet_old ∪ explode))

-- def mixLast {t : ℕ} (state : Vector (F p) t) (M : Vector (Vector (F p) t) t) (s : ℕ) : F p :=
--   (state.zipWith (fun (sj : F p) (row : Vector (F p) t) ↦ row[s]'sorry * sj) M).sum

def ex₁₂ (vec : Vector Nat 4) : Option Unit := do
  let state : Vector Nat 2 := #v[1, 2]
  let M : Vector (Vector ℕ 2) 2 := #v[#v[1, 2], #v[3, 4]]
  let res :=
    (state.zipWith (fun (sj : ℕ) (row : Vector ℕ 2) ↦ row[0]'sorry * sj) M).sum
  eq0 res

/--
info: Compiled:
fun vec => eq0 7
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do compileExampleJustSym ``ex₁₂ (←(zeta ∪ compilerWtf ∪ explode ∪ zipWith ∪ sum ∪ getElem))


def ex₁₃ (vec : Vector Nat 4) : Option Unit := do
  let t := 2
  let state : Vector Nat t := #v[1, 2]
  let S : Vector Nat 6 := #v[3, 4, 5, 6, 7, 8]
  let base : ℕ := (2 * 2 - 1) * 1
  let s' : Vector _ t := ⟨S.extract base (base+t) |>.toArray, sorry⟩
  let dotProduct := (state.zipWith (· * ·) s').sum
  let tail := (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]'sorry * S[base + t + i]'sorry)
  let res : Vector Nat 2 := ⟨#[dotProduct] ++ tail.toArray, sorry⟩
  eq0 res[0]

/--
info: Compiled:
fun vec => eq0 20
-/
#guard_msgs(info, whitespace := lax, drop warning) in
#eval spoon <| do
  compileExampleJustSym ``ex₁₃
    (←(zeta ∪ compilerWtf ∪ explode ∪ zipWith ∪ sum ∪ extract ∪ toArray ∪ mapIdx ∪ append ∪ getElem ∪ drop ∪ extract))

end ExampruSym

end Clap.Compiler
