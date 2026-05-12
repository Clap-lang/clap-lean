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

abbrev ExprS := Expr × Expr ⊕ Expr

def matchBinds (e : Expr) : Option (Expr × Expr) :=
  if let (``Bind.bind, ⟨_ :: _ :: _ :: _ :: e :: k :: _⟩) := e.getAppFnArgs then some (e, k)
  else
  if let (``Option.bind, ⟨_ :: _ :: e :: k :: []⟩) := e.getAppFnArgs then some (e, k)
  else none

/--
For the purposes of reporting, we bias chains of non-ground expressions to the right.
-/
partial def isGroundTerm (e : Expr) : Sym.Simp.SimpM (Option Expr) := do
  if let .lam name type body bi := e then
    withLocalDecl name bi type fun fvar =>
      isGroundTerm (body.instantiate1 fvar)
  else
  if let some (e,k) := matchBinds e then
    return andThen (←isGroundTerm e) (←isGroundTerm k)
  else
  if let (``Option.some, ⟨_ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Pure.pure, ⟨_ :: _ :: _ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Clap.Lang.Core.eq0, ⟨_ :: _ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Clap.Lang.Core.num2bits, ⟨_ :: _ :: _ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Clap.Lang.Core.isZero, ⟨_ :: _ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Clap.Lang.Core.share, ⟨_ :: _ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Vector.mk, ⟨_ :: _ :: e :: _ :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``Array.mk, ⟨_ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``List.toArray, ⟨_ :: e :: _⟩) := e.getAppFnArgs then
    isGroundTerm e
  else
  if let (``List.nil, _) := e.getAppFnArgs then
    return .none
  else
  if let (``List.cons, ⟨_ :: hd :: tl :: _⟩) := e.getAppFnArgs then
    return andThen (←isGroundTerm hd) (←isGroundTerm tl)
  if let (``OfNat.ofNat, _) := e.getAppFnArgs then
    return .none
  else
  if let .fvar _ := e then
    return .none
  else
  if let (``GetElem.getElem, ⟨_ :: _ :: _ :: _ :: _ :: coll :: elem :: _ :: _⟩) := e.getAppFnArgs then -- TODO: Do we want to allow only `<circuit input>[i]`?
    return andThen (if coll.isFVar then .none else .some e) (←isGroundTerm elem)
  else
  if let (``HAdd.hAdd, ⟨_ :: _ :: _ :: _ :: l :: r :: _⟩) := e.getAppFnArgs then
    let l ← isGroundTerm l
    let r ← isGroundTerm r
    return andThen l r
  else
  if let (``HMul.hMul, ⟨_ :: _ :: _ :: _ :: l :: r :: _⟩) := e.getAppFnArgs then
    let l ← isGroundTerm l
    let r ← isGroundTerm r
    return andThen l r
  else
  if let (``HSub.hSub, ⟨_ :: _ :: _ :: _ :: l :: r :: _⟩) := e.getAppFnArgs then
    let l ← isGroundTerm l
    let r ← isGroundTerm r
    return andThen l r
  else
    return .some e
  where andThen (e₁ e₂ : Option Expr) : Option Expr :=
    match e₁, e₂ with
    | .none, .none => .none
    | .none, .some e | .some e, .none => .some e
    | .some _, .some e => .some e

def ExprS.pretty (e : ExprS) : Sym.Simp.SimpM String := do
  match e with
  | .inl (e, binder) => return s!"λ {binder} ↦ {←PrettyPrinter.ppExpr e}"
  | .inr e => PrettyPrinter.ppExpr e <&> Format.pretty

def _root_.Lean.Expr.isBind (e : Expr) : Sym.Simp.SimpM Bool := do
  return e.isAppOf ``Bind.bind || e.isAppOf ``Option.bind

def _root_.Lean.Expr.getBindArgs? (e : Expr) : Sym.Simp.SimpM (Option (Expr × Expr)) := do
  -- If `e` is not `λ _ ↦ _`, then `lambdaTelescope = id`.
  lambdaTelescope e fun arg e ↦ do
    if !(←e.isBind) then return .none
    let firstExplicitArg := (←getFunInfo e.getAppFn).paramInfo.findIdx (·.binderInfo.isExplicit)
    let bindArgs := e.getAppArgs
    return .some (
      bindArgs[firstExplicitArg]!,
      bindArgs[firstExplicitArg + 1]!
    )

def _root_.Lean.Expr.mkBind (l r : Expr) (m? : Name := ``Option.bind) : Sym.Simp.SimpM Expr := do
  mkAppM m? #[l, r]

private def treeEmoji : String := "🌲"
private def stopEmoji : String := "🛑"

instance {m} [Monad m] : Union (m Sym.Simp.Methods) where
  union a b := do return (←a) ∪ (←b)

def isUnital (e : Expr) : Sym.Simp.SimpM Bool := do
  let eT ← inferType e
  if ← isDefEq eT q(Unit) then return true
  let_expr Vector _ sz := eT | return false
  let sz' ← Sym.simp sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground.\nExpr:\n{e}"
  | .some n => return n == 0

mutual

private partial def down (reduce : Expr → Sym.Simp.SimpM Expr)
                         (reduceOuter : Expr → Sym.Simp.SimpM Expr)
                         (stack : List ExprS) (todo : Expr) : Sym.Simp.SimpM Expr := do
  if let .some (l, r) ← todo.getBindArgs?
  then
    trace[Clap.Compile.down] "\npush [→]:\n{r}\ngo [↓]:\n{l}"
    down reduce reduceOuter (.inr r :: stack) l
  else
    let simped ← reduce todo
    if simped != todo
    then
      trace[Clap.Compile.simp] "[↓] {checkEmoji}\n{todo}\n==>\n{simped}"
      trace[Clap.Compile.down] "\ngo [↓]:\n{simped}"
      down reduce reduceOuter stack simped
    else
      trace[Clap.Compile.simp.fail] "[↓] {crossEmoji}\n{todo}"
      trace[Clap.Compile.down] "\ngo [↑]:\n{todo}"
      match ←isGroundTerm todo with
      | .some e => trace[Clap.Compile.simp.warnDownNotGround] "{stopEmoji} [↓] stopped:\n{e}"
      | .none => pure ()
      up reduce reduceOuter stack todo

private partial def up (reduce : Expr → Sym.Simp.SimpM Expr)
                       (reduceOuter : Expr → Sym.Simp.SimpM Expr)
                       (stack : List ExprS) (done : Expr) : Sym.Simp.SimpM Expr := do
  match stack with
  | [] =>
    trace[Clap.Compile.up] "Done"
    -- logInfo m!"DONE: {done}"
    -- logInfo m!"REPR: {repr done}"
    trace[Clap.Compile.up]
      "This should go to debug tracing. Simped done:\n{←reduce done}"
    return done
  | .inr r :: stack =>
    lambdaTelescopeOne! r fun arg body ↦ do
      -- match ←isGroundTerm done with
      -- | .some e => throwError m!"{bombEmoji} Not ground:\n{e}\nin:\n{done}"
      -- | .none =>
      trace[Clap.Compile.up] "\npush [←]:\n{(done, arg)}\ngo [↓]:\n{body}"
      down reduce reduceOuter (.inl (done, arg) :: stack) body
  | .inl l :: stack => do
    let bind ← mkBindWith l done
    let up := up reduce reduceOuter stack
    if ← isUnital l.2
    then trace[Clap.Compile.up] "\ngo [↑]:\n{bind}"
         up bind
    else trace[Clap.Compile.simp] "Binding value: {l.2} {bind}"
         let simped ← reduceOuter bind
        --  trace[Clap.Compile.simp] "WE MADE IT"
         if simped != bind
         then trace[Clap.Compile.simp] "[↑] {checkEmoji}\n{bind}\n==>\n{simped}"
         else trace[Clap.Compile.simp.fail] "[↑] {crossEmoji}\n{bind}"
         trace[Clap.Compile.up] "\ngo [↑]:\n{simped}"
         up simped
  where mkBindWith (stackEntry : Expr × Expr) (cont : Expr)
                   (m? : Name := ``Option.bind) : Sym.Simp.SimpM Expr := do
    Sym.mkLambdaFVarsS #[stackEntry.2] cont >>= stackEntry.1.mkBind (m? := m?)

end

open Simp API in
def compile (e : Expr) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Expr := do
  withTraceNode `Clap.Compile formatExprWith do
  lambdaTelescope e fun args e ↦ do
    let compiled ← down
      (reduce      := simplify simpset)
      (reduceOuter := simplify (simpset ∪ (←compilerSet)))
      (stack       := [])
      (todo        := e)
    Sym.mkLambdaFVarsS args compiled
  where
    compilerSet : MetaM Sym.Simp.Methods :=
      Sym.mkMethods #[
        ``Option.bind_assoc, ``bind_assoc,
        ``Option.pure_def,
        ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
        ``Option.map_eq_map, ``Option.map_some
      ]

namespace CompileSets

section

open Simp API

namespace Logic

def cases :=
  SimpSet.withAllPost #[
    ``dite_false, ``ite_false,

    ``dite_true, ``ite_true    
  ]

end Logic

namespace Nat

def arith :=
  SimpSet.withAllPost #[
    ``Nat.reduceMul, ``Nat.reduceDiv,
    ``Nat.reduceAdd, ``Nat.reduceSub,
    ``Nat.zero_add, ``Nat.add_zero,
    ``Nat.one_mul, ``Nat.mul_one
  ]

end Nat

namespace List

dsimproc_decl reduceRange (List.range _) := fun e ↦ do
  let_expr _root_.List.range k ← e | return .continue
  let ctx ← Simp.getContext
  let ctx ← ctx.setConfig {ctx.config with singlePass := false}
  withTheReader Simp.Context (fun _ ↦ ctx) do
  -- logInfo m!"k: {k} simped: {(←simp k).expr}"
  match (←simp k).expr.nat? with
  | .none => logError m!"{(←simp k).expr} is not ground"
             return .done e
  | .some n => let l := _root_.List.range n
               return .visit (Lean.toExpr l)

def range : SimpSet :=
  {
    pos := #[(``reduceRange, .Pre)]
  }

end List

namespace Array

dsimproc_decl reduceRange (Array.range _) := fun e ↦ do
  let_expr _root_.Array.range k ← e | return .continue
  let ctx ← Simp.getContext
  let ctx ← ctx.setConfig {ctx.config with singlePass := false}
  withTheReader Simp.Context (fun _ ↦ ctx) do
  match (←simp k).expr.nat? with
  | .none => logError m!"{(←simp k).expr} is not ground"
             return .done e
  | .some n => let l := _root_.Array.range n
               return .visit (Lean.toExpr l)

def range : SimpSet :=
  {
    pos := #[(``reduceRange, .Pre)]
  }

end Array

namespace Vector

def explode : SimpSet :=
  {
    pos := #[(``explodeVector, .Post), (``dontExplodeVector, .Pre)]
  }

def foldlM : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.foldlM_mk, ``List.foldlM_toArray,

    ``List.foldlM_cons, ``List.foldlM_nil
  ]

def getElem : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.getElem_mk, ``List.getElem_toArray,

    ``List.getElem_cons_zero, ``List.getElem_cons_succ,
  ]

-- example {inputs : Vector Nat 2} {a} {a_2} : #v[a, #v[a_2 * (inputs[1] + 66)][0]] = sorry := by
  -- rw [Vector.getElem_mk]

  -- simp +singlePass only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]

def mapOptim : SimpSet :=
  {
    pos := #[(``List.map_id, .Pre)]
  }    

def map : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.map_mk, ``List.map_toArray,
    
    ``List.map_cons, ``List.map_nil
  ] ∪ mapOptim

def mapIdx : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.mapIdx_mk, ``List.mapIdx_toArray,
    
    ``List.mapIdx_cons, ``List.mapIdx_nil
  ]

def zipWith : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.mk_zipWith_mk, ``List.zipWith_toArray,
    
    ``List.zipWith_cons_cons, ``List.zipWith_nil_left, ``List.zipWith_nil_right
  ]

-- dsimproc_decl rwMk_append_mk (Vector.mk _ _ ++ Vector.mk _ _) := fun e ↦ do
--   let x ← e.runTactic (←`(tactic| rw [$(mkIdent ``Vector.mk_append_mk):ident]))
--   return .visit x

-- def append : SimpSet :=
--   SimpSet.withAllPost #[
--     ``rwMk_append_mk, ``List.append_toArray, -- ``Vector.mk_append_mk

--     ``List.cons_append, ``List.nil_append
--   ]

dsimproc_decl rwMk_append_mk (Vector.mk _ _ ++ Vector.mk _ _) := fun e ↦ do
  let x ← e.runTactic (←`(tactic| rw [$(mkIdent ``Vector.mk_append_mk):ident]))
  return .visit x

def append : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.mk_append_mk, ``List.append_toArray,

    ``List.cons_append, ``List.nil_append,

    ``List.append_nil
  ]

def take : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.take_mk, ``List.take_toArray,

    ``List.take_succ_cons, ``List.take_nil, ``List.take_zero
  ]

def size : SimpSet :=
  SimpSet.withAllPost #[
   ``Vector.size_toArray, ``List.size_toArray,
   ``List.length_cons, ``List.length_nil
  ]

theorem _root_.List.drop_toArray {α} {l : List α} {i} :
  l.toArray.drop i = (l.drop i).toArray := by
  simp only [
    Array.drop_eq_extract, List.size_toArray, List.extract_toArray,
    List.extract_eq_take_drop, Array.mk.injEq
  ]
  rw [←List.extract_eq_take_drop, List.drop_eq_extract]

def drop : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.drop_mk, ``_root_.List.drop_toArray,

    ``List.drop_succ_cons, ``List.drop_zero, ``List.drop_nil, ``List.drop_zero
  ]

def extract : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.extract_mk, ``List.extract_toArray,
    
    ``List.extract_eq_take_drop
  ] ∪ drop ∪ take 

def set : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.set_mk, ``List.set_toArray,
    
    ``List.set_cons_succ, ``List.set_cons_zero,
  ]

def foldl : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.foldl_mk, ``List.foldl_toArray,

    ``List.foldl_cons, ``List.foldl_nil
  ]

dsimproc_decl erwFoldr_toArray (Array.foldr _ _ _ _ _) := fun e ↦ do
  let_expr Array.foldr _ _ _ _ arr _ _ := e | return .continue
  let_expr List.toArray _ _ := arr | return .continue
  let x ← e.runTactic (←`(tactic| erw [$(mkIdent ``List.foldr_toArray):ident]))
  return .visit x

def foldr : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.foldr_mk, ``erwFoldr_toArray,

    ``List.foldr_cons, ``List.foldr_nil
  ] ∪ size

def sum : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.sum_eq_foldr
  ] ∪ foldr

@[simp]
theorem _root_.Vector.mapM_singleton {α} {β} {m} [Monad m] [LawfulMonad m] {f : α → m β} {x} :
  #v[x].mapM f = f x >>= (pure #v[·]) := by
  apply Vector.map_toArray_inj.mp; simp

@[simp]
theorem _root_.Vector.mapM_nil {α β} {m} [Monad m] [LawfulMonad m] {f : α → m β} :
  #v[].mapM f = pure #v[] := by simp

@[simp↓ high]
theorem _root_.Vector.mapM_mk_singleton_append {m} [Monad m] [LawfulMonad m] {α} {β} {n} {f : α → m β}
  {v : Vector α n} {x : α} :
  (#v[x] ++ v).mapM f = (return #v[(←f x)] ++ (←v.mapM f)) := by simp

-- def liftTermElabM {α} (m : TermElabM α) : Sym.Simp.SimpM α := liftM m.run'

-- /--
-- 0. Only for `Vector.mapM f xs`.
-- 1. Vector.mapM f #v[a, b, c] → Vector.mapM f (#v[a] ++ #v[b, c])
-- 2. Vector.mapM f (#v[x] ++ v) = do
--      let __do_lift ← f x
--      let __do_lift_1 ← Vector.mapM f v
--      pure (#v[__do_lift] ++ __do_lift_1)
-- -/
-- dsimproc_decl _root_.Vector.mapM_mk_eq_append (_root_.Vector.mapM _ _) := fun e ↦ do
--   let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .continue
--   let_expr _root_.Vector.mk _ sz arr _ := vec | return .continue
--   let_expr List.toArray _ l := arr | return .continue
--   let_expr List.cons t hd tl := l | return .continue
--   let szN := (←simp sz).expr.nat?.get!
--   if szN <= 1 then return .continue
--   let hd ← liftTermElabM (mkVecLit (←mkListLit t [hd]) (mkNatLit 1))
--   let tl ← liftTermElabM (mkVecLit tl (toExpr (szN - 1)))
--   let consHdTl ← mkAppM ``HAppend.hAppend #[hd, tl]
--   let mapM ← mkAppM ``_root_.Vector.mapM #[f, consHdTl]  
--   let consMapM ← mapM.runTactic (←`(tactic| rw[$(mkIdent ``Vector.mapM_mk_singleton_append):ident]))
--   return .visit consMapM

-- /--
-- 0. Only for `Vector.mapM f xs`.
-- 1. Vector.mapM f #v[a, b, c] → Vector.mapM f (#v[a] ++ #v[b, c])
-- 2. Vector.mapM f (#v[x] ++ v) = do
--      let __do_lift ← f x
--      let __do_lift_1 ← Vector.mapM f v
--      pure (#v[__do_lift] ++ __do_lift_1)
-- -/
-- def _root_.Vector.mapM_mk_eq_append : Sym.Simp.Simproc := fun e ↦ do
--   let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .rfl
--   let_expr _root_.Vector.mk _ sz arr _ := vec | return .rfl
--   let_expr List.toArray _ l := arr | return .rfl
--   let_expr List.cons t hd tl := l | return .rfl
--   let sz' ← Sym.simp sz
--   match (sz'.getResultExpr sz).nat? with
--   | .none => throwError m!"{sz} does not simplify to ground"
--   | .some szN =>
--     if szN == 0 then return .rfl
--     let hd ← liftTermElabM (mkVecLit (←mkListLit t [hd]) (mkNatLit 1))
--     let tl ← liftTermElabM (mkVecLit tl (toExpr (szN - 1)))
--     let consHdTl ← mkAppM ``HAppend.hAppend #[hd, tl]
--     let mapM ← mkAppM ``_root_.Vector.mapM #[f, consHdTl]
--     -- let consMapM ← mapM.runTactic (←`(tactic| rw [$(mkIdent ``Vector.mapM_mk_singleton_append):ident]))
--     -- TODO: Definitely wrong, we need `Vector.mapM_mk_singleton_append` _at least_.
--     -- return .step consMapM (←Sym.mkEqRefl e)
--     return .step mapM (←Sym.mkEqRefl e)

-- def mapM : SimpSet :=
--   SimpSet.withAllPost #[
--     ``Vector.mapM_mk_singleton_append,
    
--     ``Vector.mapM_mk_eq_append, ``Vector.mapM_mk_empty

--     -- ``map_pure, ``Option.map_eq_map, ``Option.map_some, ``Option.bind_eq_bind
--   ] ∪ append ∪ getElem

end Vector

end

end CompileSets

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
  -- logInfo m!"post procs: {procs}\nthms: {thms}"
  let procs ← andThen procs.toArray
  return { post := (←mkSimprocFor thms.toArray d) >> procs }

def mkPreMethods (declNames : Array Name)
                 (d : Discharger := Sym.Simp.dischargeSimpSelf) : MetaM Methods := do
  let (procs, thms) ← declNames.toList.partitionM (liftM ∘ isSimproc)
  -- logInfo m!"pre procs: {procs}"
  let procs ← andThen procs.toArray
  return { pre := (←mkSimprocFor thms.toArray d) >> procs }

elab "sym_simp" "[" declNamesPre:ident,* "]" "[" declNamesPost:ident,* "]" : tactic => do
  let rewritePre ← mkPreMethods (←declNamesPre.getElems.mapM fun s ↦ realizeGlobalConstNoOverload s.raw)
  let rewritePost ← mkPostMethods (←declNamesPost.getElems.mapM fun s ↦ realizeGlobalConstNoOverload s.raw)
  -- let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  -- let methods : Sym.Simp.Methods := {
  --   pre  := Sym.Simp.simpControl >> rewritePre.pre
  --   post := Sym.Simp.evalGround >> rewritePost.post
  -- }
  let methods : Sym.Simp.Methods := {
    pre  := rewritePre.pre
    post := rewritePost.post
  }
  Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

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
This is more or less `Lean.meta.Tactic.Cbv.zetaReduce`, which seems to not be exported.

In `Sym`, maybe we can choose to not `zeta` certain things without breaking `simp`?
-/
private def zetaReduce : Simproc := fun e => do
  let .letE _ _ value body _ := e | return .rfl
  let new := expandLet body #[value]
  let new ← Sym.share new
  return .step new (←Sym.mkEqRefl new)

def zeta : MetaM Methods := do
  return {
    pre := zetaReduce
  }

def ground : MetaM Methods := do
  return {
    post := evalGround
  }

end General

namespace Vector

def append : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_append_mk, ``List.append_toArray,

    ``List.cons_append, ``List.nil_append, ``List.append_nil,

    ``Compiler.explodeVectorAppend
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
  let_expr GetElem.getElem _ _ _ _ _ coll i h := e | return .rfl
  let_expr Vector.mk _ _ arr h := coll | return .rfl
  logInfo m!"This is getElem on Vector.mk:\n({coll})[{i}]"
  logInfo m!"e:\n{e}"
  
  let thm ← mkTheoremFromDecl ``Vector.getElem_mk
  -- logInfo m!"thm declName: {thm.declName}"
  -- logInfo m!"thm expr: {thm.expr}"
  logInfo m!"thm pattern: {thm.pattern.pattern}"
  -- logInfo m!"thm rhs: {thm.rhs}"
  -- let thmrw ← thm.rewrite e
  -- match thmrw with
  -- | .rfl _ _ => logInfo m!"Rewrite failed."
  -- | .step e' _ _ _ => logInfo m!"Success. e: {e'}"
  -- match ←thm.pattern.unify? e with
  -- | .none => logInfo m!"NO UNIFY"
  -- | .some res => logInfo m!"UNIFY OK!:\n{res.args}"
  
  let esimped ← e.runTactic (←`(tactic|rw! (castMode := .all) [Nat.add_zero]))
  -- let esimped := (← (Sym.simp e (←mkPostMethods #[``Nat.add_zero]))).getResultExpr e

  match ← thm.pattern.match? e with
  | .none => logInfo m!"NO MATCH:\n{e}\n=?=\n{thm.pattern.pattern}"
  | .some e' => logInfo m!"OK!: {e'.args}"

  match ← thm.pattern.match? esimped with
  | .none => logInfo m!"NO MATCH SIMPED:\n{esimped}\n=?=\n{thm.pattern.pattern}"
  | .some e' => logInfo m!"OK!: {e'.args}\n"
  -- match ← thm.pattern.match? ((← unfoldReducible (← instantiateMVars e))) with
  -- | .none => logInfo m!"did not match"
  -- | .some e => logInfo m!"OK!: {e.args}"

  return .rfl

def getElem : MetaM Methods :=
  mkPostMethods #[
    -- ``Vector.getElem_mk, ``List.getElem_toArray,

    -- ``List.getElem_cons_zero, ``List.getElem_cons_succ,

    ``getElemDbg
  ]

def map : MetaM Methods :=
  mkPostMethods #[
    ``Vector.map_mk, ``List.map_toArray,
    
    ``List.map_cons, ``List.map_nil,

    ``Compiler.explodeVectorMap
  ] ∪ mapOptim
  where
    mapOptim : MetaM Methods := mkPreMethods #[``List.map_id]

/--
0. Only for `Vector.mapM f xs`.
1. Vector.mapM f #v[a, b, c] → Vector.mapM f (#v[a] ++ #v[b, c])
2. Vector.mapM f (#v[x] ++ v) = do
     let __do_lift ← f x
     let __do_lift_1 ← Vector.mapM f v
     pure (#v[__do_lift] ++ __do_lift_1)
-/
def _root_.Vector.mapM_mk_eq_append : Sym.Simp.Simproc := fun e ↦ do
  let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .rfl
  let_expr _root_.Vector.mk _ sz arr _ := vec | return .rfl
  unless arr.isAppOf ``List.toArray || arr.isAppOf ``Array.mk do return .rfl
  let l ← arr.getAppArgs[1]?.getDM (unreachable!)
  let_expr List.cons t hd tl := l | return .rfl
  let sz' ← Sym.simp sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e}"
  | .some szN =>
    if szN == 0 then return .rfl
    let hd ← mkVecLit (←mkListLit t [hd]) (mkNatLit 1)
    let tl ← mkVecLit tl (toExpr (szN - 1))
    let consHdTl ← mkAppM ``HAppend.hAppend #[hd, tl]
    let mapM ← mkAppM ``_root_.Vector.mapM #[f, consHdTl]
    -- TODO: I am guessing this is... slow?
    let consMapM ← mapM.runTactic (←`(tactic| rw[$(mkIdent ``Vector.mapM_mk_singleton_append):ident]))
    -- TODO: Puh-ROOF!
    return .step consMapM (←mkSorry (←mkEq e mapM) false)

/--
`Vector.mapM_mk_singleton_append` is a part of `Vector.mapM_mk_append` to ensure that
the transformation `#v[a, b] ==> #v[a] ++ #v[b]` does not get undone by `Vector.mk_append_mk`.
-/
def mapM : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk_eq_append, ``Vector.mapM_nil,

    ``Compiler.explodeVectorMapM
  ] ∪ append ∪ getElem

end Vector

end

end SymSets

def compileExample (ex : Name) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Format := do
  compile (((←getEnv).find? ex).get!.value!) simpset >>= (liftM ∘ PrettyPrinter.ppExpr)

def eq0 (e : Nat) : Option Unit := .some ()

def spoon (m : Sym.Simp.SimpM Format) : MetaM Format :=
  m.run' {} |>.run

namespace ExampruSym

open SymSets Monad General Vector

def ex₀ : Option Unit := do
  eq0 0
  eq0 1
  let _res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 2)
  eq0 3
  return ()

/--
info: (eq0 0).bind fun x =>
  (eq0 1).bind fun x =>
    ((eq0 2).bind fun init => (eq0 2).bind fun init => pure init).bind fun _res => (eq0 3).bind fun x => pure PUnit.unit
-/
#guard_msgs in
#eval spoon <| do compileExample ``ex₀ (←foldlM)

-- set_option trace.Clap.Compile true

def ex₁ (vec : Vector Nat 3) : Option Unit := do
  eq0 <| GetElem.getElem #v[4] 0 (by sorry)
  -- eq0 #v[4, 5][0]

-- /-- info: fun vec => eq0 4 -/
-- #guard_msgs in
-- #eval spoon <| do compileExample ``ex₁ (←getElem)

-- def ex₂ (vec : Vector Nat 3) : Option Unit := do
--   let x := (vec ++ vec)[0]
--   eq0 x

-- /-- info: fun vec => eq0 vec[0] -/
-- #guard_msgs in
-- #eval spoon <| do compileExample ``ex₂ (←(append ∪ zeta ∪ getElem))

-- def ex₃ (vec : Vector Nat 3) : Option Unit := do
--   let x := vec.map (·+1)
--   eq0 x[0]

/-- info: fun vec => eq0 (vec[0] + 1) -/
-- #guard_msgs in
-- #eval spoon <| do compileExample ``ex₃ (←(map ∪ zeta ∪ getElem))

def ex₄ (vec : Vector Nat 1) : Option Unit := do
  let x ← vec.mapM (fun x ↦ return x + 1)
  eq0 x[0]

#check Nat.sub_add_cancel
set_option trace.Clap.Compile true
set_option pp.proofs true in
#eval spoon <| do compileExample ``ex₄ (←(ground ∪ mapM ∪ getElem ∪ zeta))

-- not ok
-- @GetElem.getElem
--   (Vector ℕ 1)
--   ℕ
--   ℕ
--   (fun x i => i < 1)
--   instGetElemNatLt
--   (Vector.mk - CAREFUL: The type of this has to match the type of GetElem up to defeq.
--     { toList := [vec[0] + 1] }
--     (Eq.trans <some eq> ▸ mk_append_mk._proof_1 rfl sorry))
--   0
--   ex₄._proof_2

-- ok
-- @GetElem.getElem
--   (Vector ℕ 2) 
--   ℕ
--   ℕ
--   (fun x i => i < 2)
--   instGetElemNatLt
--   (Vector.mk
--     { toList := [4, 5] }
--     ex₁._proof_2)
--   0
--   ex₁._proof_3

-- @GetElem.getElem
--   (Vector #5 #4)
--   ℕ
--   #5
--   (fun x i => i < #4)
--   instGetElemNatLt
--   (Vector.mk #3 #2)
--   #1
--   #0

#exit

example {vec : Vector Nat 1} : ex₄ vec = sorry := by
  unfold ex₄
  rcases vec with ⟨arr, h⟩
  rcases arr with ⟨l⟩
  rcases l with _ | ⟨hd, _ | ⟨_, _⟩⟩
  simp at h
  sym_simp [] [Option.pure_def, mapM_singleton, Option.bind_eq_bind, Option.bind_some, getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero]
  


example {vec : Vector Nat 1} : eq0
  (Vector.mk (n := 1 + 0) { toList := [vec[0] + 1] } (Eq.trans (List.append_toArray [vec[0] + 1] []) (congrArg Array.mk (List.append_nil [vec[0] + 1])) ▸
  mk_append_mk._proof_1 rfl (of_eq_true (Eq.trans (congrFun' (congrArg Eq List.size_toArray) 0) (eq_self 0))) : (fun toArray : Array _ => toArray.size = 1 + 0) { toList := [vec[0] + 1] }))[0] = sorry := by
  -- rw [getElem_mk]
  sym_simp [] [getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  
  done


#check Vector.mapM_mk_eq_append
/--
this is for size 3
-/
example {vec : Vector Nat 1} : ex₄ vec = sorry := by
  unfold ex₄
  sym_simp [dontExplodeVector] [explodeVector]
  sym_simp [] [Vector.mapM_mk_eq_append]
  sym_simp [] [Vector.mapM_nil]
  sym_simp [] [Option.bind_assoc, bind_assoc,
    Option.pure_def,
    Option.bind_eq_bind, Option.bind_fun_some, Option.bind_some, bind_pure, pure_bind,
    Option.map_eq_map, Option.map_some]
  sym_simp [] [Vector.mk_append_mk]
  simp
  simp
  simp [Vector.mk_append_mk]
  rw [Vector.mk_append_mk]
  simp
  
  
  simp only [Vector.mk_append_mk]


  -- simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  -- sym_simp [] [Vector.mk_append_mk]
  
  -- simp
  simp
  
  
  
  -- sym_simp [dontExplodeVector] [explodeVector, Vector.mapM_mk_eq_append]
  -- sym_simp [] [Vector.mapM_singleton, Vector.mapM_mk_singleton_append]
  
  
  

  simp only [Nat.reduceAdd, Option.pure_def, Option.bind_eq_bind, Option.bind_some, getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero]


  sorry

-- example :
--   #[4, 5][0] = sorry := by
--   sym_simp [List.getElem_toArray]

-- example {v : Vector Nat 3} : ex₁ v = sorry := by
--   unfold ex₁
--   sym_simp [Vector.getElem_mk, List.getElem_toArray]

-- def getElem : MetaM Lean.Meta.Sym.Simp.Methods :=
--   mkPostMethods #[
--     ``List.getElem_toArray
--   ]

-- def getElem' : MetaM Lean.Meta.Sym.Simp.Methods := do
--   let rewrite ← Sym.mkSimprocFor #[``List.getElem_toArray, ``Vector.getElem_mk] Sym.Simp.dischargeSimpSelf
--   return {
--     post := rewrite
--   }

-- #eval spoon <| do compileExample ``ex₁ (←getElem')

end ExampruSym

namespace Exampru

def ex₀ : Expr := q(
  do eq0 0
     eq0 1
     let _res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 2)
     eq0 3
     return ()
)                    
-- set_option trace.Clap.Compile true
-- /--
-- info: (eq0 0).bind fun x =>
--   (eq0 1).bind fun x =>
--     ((eq0 2).bind fun init => (eq0 2).bind fun init => pure init).bind fun _res => (eq0 3).bind fun x => pure ()
-- -/
-- #guard_msgs in
-- #eval show MetaM _ from do
--   let res := compile ex₀
--     (SimpSet.withAllPost #[``List.foldlM_cons, ``List.foldlM_nil]) >>=
--     (liftM ∘ PrettyPrinter.ppExpr)
--   res.run' default |>.run

def ex₁ (n : Nat) : Option Unit := do
  eq0 0
  let res ← (#v[0, 1].foldlM (fun acc _ ↦ return acc) #v[n, 6])
  let res' := res.map (·+1)
  eq0 (res'[0])
  eq0 (res'[1])
  return ()

open CompileSets Vector Logic

set_option trace.Clap.Compile true

/--
info: fun n => do
  eq0 0
  (eq0 (n + 1)).bind fun a => (eq0 7).bind fun a => some ()
-/
#guard_msgs in
#eval spoon <| compileExample ``ex₁ (foldlM ∪ map ∪ getElem ∪ explode)

-- def ex₂ (vec : Vector Nat 4) : Option Unit := do
--   eq0 ((vec ++ vec)[0])
--   eq0 0
--   let _res ← vec.foldlM (fun acc x ↦ do eq0 x; acc) (eq0 4)
--   eq0 4

-- /--
-- info: fun vec => do
--   eq0 vec[0]
--   eq0 0
--   (eq0 vec[0]).bind fun a =>
--       (eq0 4).bind fun a => (eq0 vec[1]).bind fun a => (eq0 vec[2]).bind fun a => (eq0 vec[3]).bind fun a => eq0 4
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₂
--         (foldlM ∪ getElem ∪ map ∪ explode ∪ append)

-- def ex₃ (vec : Vector Nat 3) : Option Unit := do
--   eq0 ((vec ++ vec)[0])
--   eq0 0
--   let res := vec.mapIdx fun i _ ↦ i
--   eq0 res[0]
--   eq0 res[1]
--   eq0 res[2]

-- /--
-- info: fun vec => do
--   eq0 vec[0]
--   eq0 0
--   eq0 0
--   eq0 1
--   eq0 2
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₃
--         (foldlM ∪ getElem ∪ map ∪ explode ∪ append ∪ mapIdx)

def ex₄ (vec : Vector Nat 3) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := vec.zipWith (bs := vec.map (·+1)) fun x y ↦ x + y
  eq0 res[0]
  eq0 res[1]
  eq0 res[2]

/--
info: fun vec => do
  eq0 vec[0]
  eq0 0
  eq0 (2 * vec[0] + 1)
  eq0 (2 * vec[1] + 1)
  eq0 (2 * vec[2] + 1)
-/
#guard_msgs in
#eval spoon <| compileExample ``ex₄
        (foldlM ∪ getElem ∪ map ∪ explode ∪ append ∪ mapIdx ∪ zipWith)
  
-- def ex₅ (vec : Vector Nat 3) : Option Unit := do
--   eq0 ((vec ++ vec)[0])
--   eq0 0
--   let res := (vec.drop 1).take 1
--   eq0 res[0]

-- /--
-- info: fun vec => do
--   eq0 vec[0]
--   eq0 0
--   eq0 vec[1]
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₅
--         (foldlM ∪ getElem ∪ map ∪ explode ∪ append ∪ mapIdx ∪ zipWith ∪ take ∪ drop)

-- def ex₆ (vec : Vector Nat 3) : Option Unit := do
--   eq0 ((vec ++ vec)[0])
--   eq0 0
--   let res := vec.sum
--   eq0 res

-- /--
-- info: fun vec => do
--   eq0 vec[0]
--   eq0 0
--   eq0 (vec[0] + vec[1] + vec[2])
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₆
--         (explode ∪ append  ∪ sum)

-- def ex₇ (vec : Vector Nat 3) : Option Unit := do
--   let vec := vec.zipWith (·+·) #v[1, 5, 10]
--   eq0 42
--   let res ← vec.mapM (fun n ↦ return n + 1)
--   eq0 res[0]
--   eq0 res[1]
--   eq0 res[2]

-- example {inputs : Vector Nat 2} {sigma : ℕ → Option Unit} :
--   Vector.mapM sigma
--       #v[0 + 6745197990210204598374042828761989596302876299545964402857411729872131034734,
--         inputs[0] + 426281677759936592021316809065178817848084678679510574715894138690250139748,
--         inputs[1] + 4014188762916583598888942667424965430287497824629657219807941460227372577781] =
--   sorry := by
--   simp +singlePass [Vector.mapM_mk_eq_append]
--   simp +singlePass [Vector.mapM_mk_eq_append]
--   simp? +singlePass [Vector.mapM_mk_eq_append]
--   done

-- def ex₈ (vec : Vector Nat 3) : Option Unit := do
--   let res := (#v[0] ++ vec).extract 1 2
--   eq0 res[0]

-- #eval compileExample ``ex₈ (append ∪ explode ∪ extract ∪ getElem)


-- def ex₉ (vec : Vector Nat 3) : Option Unit := do
--   let res := (#v[0] ++ vec).set 0 42
--   eq0 res[0]

-- #eval compileExample ``ex₉ (append ∪ explode ∪ extract ∪ getElem ∪ set)
#check Sym.simp
opaque share : Nat → Option Nat

-- example {inputs : Vector Nat 3} : ((share ((0 + 66) * (0 + 66))).bind fun a =>
--   (share (a * a)).bind fun a =>
--     (share ((inputs[0] + 66) * (inputs[0] + 66))).bind fun a_1 =>
--       (share (a_1 * a_1)).bind fun a_2 =>
--         (share ((inputs[1] + 66) * (inputs[1] + 66))).bind fun a_3 =>
--           (share (a_3 * a_3)).bind fun a_4 =>
--             some
--               #v[66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][0] + 66) +
--                   (66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][1] + 66) +
--                     (66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][2] + 66) + 0)),
--                 66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][0] + 66) +
--                   (66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][1] + 66) +
--                     (66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][2] + 66) + 0)),
--                 66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][0] + 66) +
--                   (66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][1] + 66) +
--                     (66 * ([a * (0 + 66), a_2 * (inputs[0] + 66), a_4 * (inputs[1] + 66)][2] + 66) + 0))]) = sorry := by
--   simp?
--   sorry
--   done

end Exampru

end Clap.Compiler
