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
    trace[Clap.Compile.up]
      "This should go to debug tracing. Simped done:\n{←reduce done}"
    return done
  | .inr r :: stack =>
    lambdaTelescopeOne! r fun arg body ↦ do
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
-- e : Vector (1 + 2) ==> Vector 3
-- e : Vector 3 := Eq.mp rfl e
/--
YEEEEEHAAAAAAAAW, you rootin' tootin' cowboy.
-/
def cowboyCast (e : Expr) (yourDeepestDesire : ℕ) : Sym.SymM Expr := do
  let t ← Sym.inferType e
  let_expr Vector t sz := t | throwError m!"Not a true cowboy."
  let proof ← mkEq t (←mkAppM ``Vector #[t, mkNatLit yourDeepestDesire])
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

-- `(fun x ↦ f (id x) (id y)) y` | id x == id x
-- `e : f (id y) (id y)`  [β]    | id x ≠ id x
-- `let e := incrementalShare e`
--                               | id x == id x

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

private def evalGround : Simproc := fun e ↦ do
  let e' ← Sym.Simp.evalGround {} e
  unless isSameExpr e (e'.getResultExpr e) do
    trace[Clap.Compile.simp.proc.evalGround]
      m!"\n{e}\n==>\n{e'.getResultExpr e}"
  return e'

def ground : MetaM Methods := do
  return {
    post := evalGround
  }

-- private def dbgCompilerSet : Simproc := fun e ↦ do
--   let_expr Option.bind _ _ m k := e | return .rfl
--   logInfo m!"Compiler fallback.\n{e}"
--   let thm ← mkTheoremFromDecl ``Option.bind_some
--   let pat := thm.pattern
--   logInfo m!"PAT: {pat.pattern}"
--   match ←pat.match? e with
--   | .none => logInfo m!"NO MATCH"
--              return .rfl
--   | .some stuff => logInfo m!"YES MATCH: {stuff.args}"
--                    return .rfl

def compilerSet : MetaM Sym.Simp.Methods :=
  mkPostMethods #[
    ``Option.bind_assoc, ``bind_assoc,
    ``Option.pure_def,
    ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
    ``Option.map_eq_map, ``Option.map_some,

    -- ``dbgCompilerSet
  ]

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

-- Essentially `Vector.mk_append_mk`.
private def mk_append_mk' : Simproc := fun e ↦ do
  let_expr HAppend.hAppend _ _ _ _ xs ys := e | return .rfl
  let_expr Vector t szXs := ←Sym.inferType xs | return .rfl
  let_expr Vector _ szYs := ←Sym.inferType ys | return .rfl
  let_expr Vector.mk _ _ xs _ := xs | return .rfl
  let_expr Vector.mk _ _ ys _ := ys | return .rfl
  match szXs.nat?, szYs.nat? with
  | .some szXs, .some szYs =>
    -- The trick here is to enforce _syntactically_ that `szXs + szYs` for concrete values
    -- is evaluated. `Vector.mk_append_mk` leaves `q(szXs + szYs)`.
    let append ← mkAppM ``HAppend.hAppend #[xs, ys]
    let szAppend := toExpr (szXs + szYs)
    let szAppendProof ← mkSorry (←mkEq (←mkAppM ``Array.size #[append]) szAppend) false
    let e' := mkAppN
                (.const ``Vector.mk [←getDecLevel t])
                #[t, szAppend, append, szAppendProof]
    let e' ← Compiler.Simp.reducedAndSharedInc e'
    let proof ← mkSorry (←mkEq e e') false -- Probably just `Vector.mk_append_mk` up to defeq
    trace[Clap.Compile.simp.proc.mk_append_mk]
      m!"\n{e}\n==>\n{e'}"
    return .step e' proof
  | _ , _ =>
    -- TODO: I have a feeling this sometimes misbehaves for some reason, look into this.
    -- Notably, when using `Vector.getElem_mk` 'directly', it simps more things than this guy?
    -- TODO: Sharing
    logWarning m!"{e} is an append of non-ground size (TODO: remove)"
    let thm ← mkTheoremFromDecl ``Vector.getElem_mk
    thm.rewrite e

-- def appendDbg : Sym.Simp.Simproc := fun e ↦ do
  
--   let_expr Vector.mk _ _ arr _ := e | return .rfl
--   logInfo m!"{e} makes: {arr}"
  
--   let thm ← mkTheoremFromDecl ``List.append_toArray
  
--   match ←thm.pattern.match? arr with
--   | .none => logInfo m!"{bombEmoji} Pattern:\n{thm.pattern.pattern}"
--   | .some arr => logInfo m!"{checkEmoji} Pattern:\n{arr.args}"
--   match ←thm.pattern.match? (←Compiler.Simp.preprocessExpr e) with
--   | .none => logInfo m!"{bombEmoji} Pattern:\n{thm.pattern.pattern}"
--   | .some arr => logInfo m!"{checkEmoji} Pattern:\n{arr.args}"
--   return .rfl
  

def append : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_append_mk, ``List.append_toArray,

    ``List.cons_append, ``List.nil_append, ``List.append_nil,

    ``Compiler.explodeVectorAppend,

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
  
  -- let esimped ← e.runTactic (←`(tactic|rw! (castMode := .all) [Nat.add_zero]))

  match ← thm.pattern.match? e with
  | .none => logInfo m!"NO MATCH:\n{e}\n=?=\n{thm.pattern.pattern}"
  | .some e' => logInfo m!"YOU TRIGGERED SON! OK!: {e'.args}"

  -- match ← thm.pattern.match? esimped with
  -- | .none => logInfo m!"NO MATCH SIMPED:\n{esimped}\n=?=\n{thm.pattern.pattern}"
  -- | .some e' => logInfo m!"OK!: {e'.args}\n"
  -- match ← thm.pattern.match? ((← unfoldReducible (← instantiateMVars e))) with
  -- | .none => logInfo m!"did not match"
  -- | .some e => logInfo m!"OK!: {e.args}"

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
def getElem : MetaM Methods :=
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

    ``Compiler.explodeVectorMap,
    
    ``mapDbg
  ] ∪ mapOptim
  where
    mapOptim : MetaM Methods := mkPreMethods #[``List.map_id]

def listOfArray (e : Expr) : Option Expr :=
  if e.isAppOf ``List.toArray || e.isAppOf ``Array.mk
  then .none
  else .some e.getAppArgs[1]!

open Compiler.Simp in
/--
Single step transformation. TODO: Does not play particularly nice with our top-level driver.

`Vector.mapM f #v[x₀, x₁, ..., xₘ]` ==>
`f x₀ >>= fun row₀ ↦ f x₁ >>= fun row₁ ↦ ... fun rowₘ ↦ .some #v[row₀, row₁, ..., rowₘ]`
-/
def _root_.Vector.mapM_mk_cons : Sym.Simp.Simproc := fun e ↦ do
  let time ← IO.monoMsNow
  let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .rfl
  let_expr _root_.Vector.mk t sz _ _ := vec | return .rfl
  let szSimped := (←Sym.simp sz).getResultExpr sz
  if !isSameExpr sz szSimped then logWarning m!"TODO: Had to simp length in:\n{e}"
  match szSimped.nat? with
  | .none => throwError m!"{sz} does not simplify to ground. Expr:\n{e} (TODO: Maybe this is ok.)"
  | .some szSimpedNat =>
    if szSimpedNat == 0 then return .rfl -- `Vector.mapM_mk_empty`
    let transformedList ← mkListLit t <| (List.range szSimpedNat).reverse.map .bvar
    let transformedVector ← mkVecLit transformedList szSimped
    let transformedVector? ← mkAppM ``Option.some #[transformedVector]
    /-
    Start with `.some #[.bvar sz.pred, .bvar sz.pred.pred, ..., .bvar 0]`
    Prefix a single lambda in each iteration.
    -/
    let e' ← (List.range szSimpedNat).foldrM (init := transformedVector?) fun i e ↦ do
      let elem ← getElemVectorOfIdx vec szSimpedNat i
      mkAppM ``Option.bind #[
        ←reducedAndSharedInc (f.beta #[elem]), -- TODO?: Expr.app f hdVec
        .lam (binderInfo := .default)
             (binderName := .mkSimple s!"row_{i}")
             (binderType := t)
             (body := e) -- `f vec[i] >>= fun row_{i} ↦ e`
      -- Careful, `e` contains loose bvars until the very last iteration.
      ]
    /-
    `unfoldReducible` apparently clamps (yet)-non-existant `.bvar` references if called on
    the initial `transformedVector`; ouch.

    We could build the share incrementally, but it is ever so slightly annoying considering
    we cannot `unfoldReducible` willy-nilly.
    -/
    let e' ← Sym.share (← unfoldReducible e')
    trace[Clap.Compile.simp.proc.vector_mapM_mk_cons]
      m!"\n{e}\n==>\n{e'}"
    logInfo m!"Vector.mapM_mk_cons took {(Float.ofNat (←IO.monoMsNow) - Float.ofNat time)/Float.ofNat 1000}s"
    return .step e' (←mkSorry (←mkEq e e') false)

/--
0. Only for `Vector.mapM f xs`.
1. Vector.mapM f #v[a, b, c] → Vector.mapM f (#v[a] ++ #v[b, c])
2. Vector.mapM f (#v[x] ++ v) = do
     let __do_lift ← f x
     let __do_lift_1 ← Vector.mapM f v
     pure (#v[__do_lift] ++ __do_lift_1)
-/
def _root_.Vector.mapM_mk_eq_append : Sym.Simp.Simproc := fun e ↦ do
  -- logInfo m!"Nodes: {←e.numObjs}"
  -- let α ← IO.monoMsNow
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
    let hdVec ← mkVecLit (←mkListLit t [hd]) (mkNatLit 1)
    let tl ← mkVecLit tl (toExpr (szN - 1)) -- Doing `-1` feels scary
    -- -- `let appendHdTl ← mkAppM ``HAppend.hAppend #[hdVec, tl]` makes a silly `k + 0` vector
    -- TODO: This is just a WIP-test solution, it's clearly terrible.
    let appendHdTl ← if szN == 1 then pure hdVec else mkAppM ``HAppend.hAppend #[hdVec, tl]
    let_expr Vector _ szAppendHdTl := ←Sym.inferType appendHdTl | unreachable!
    let szAppendHdTlQ : Q(ℕ) := szAppendHdTl
    let szDesired : Q(ℕ) := toExpr szN
    let proof ← mkSorry q($szAppendHdTlQ = $szDesired) false
    -- logInfo m!"will try to cowboy cast: {appendHdTl}"
    -- let thatGuy ← cowboyCast appendHdTl szN
    let thatGuy := appendHdTl
    let thisGuy := appendHdTl
    let thisGuy := thatGuy
    let mapM ← mkAppM ``_root_.Vector.mapM #[f, thisGuy]
    let theMiddleBit ←
      if szN == 1
      then mkVecLit (←mkListLit t [.bvar 1]) (mkNatLit 1)
      else pure <| mkAppN
            (.const ``HAppend.hAppend [
              ←getDecLevel (←Sym.inferType hdVec),
              ←getDecLevel (←Sym.inferType tl),
              ←getDecLevel (←Sym.inferType thisGuy)
            ]) #[
              ←Sym.inferType hdVec,
              ←Sym.inferType tl,
              ←Sym.inferType thisGuy,
              -- ←Sym.inferType appendHdTl,
              ←Sym.synthInstance (←mkAppM ``HAppend #[←Sym.inferType hdVec,←Sym.inferType tl,←Sym.inferType thisGuy,]),
              ←mkVecLit (←mkListLit t [.bvar 1]) (mkNatLit 1),
              .bvar 0
            ]
    let consMapM ←
      mkAppM ``Option.bind #[
        f.beta #[hd],
        -- Expr.app f hdVec,
        .lam `fst t
          (←mkAppM ``Option.bind #[
                     ←mkAppM ``Vector.mapM #[f, tl],
                     .lam `snd (←Sym.inferType tl)
                       (←mkAppM ``Option.some #[theMiddleBit])
                       .default
          ])
          .default 
      ]

    trace[Clap.Compile.simp.proc.vector_mapM_mk_eq_append]
      m!"\n{e}\n==>\n{consMapM}"
    let consMapM ← Compiler.Simp.reducedAndSharedInc consMapM
    return .step consMapM (←mkSorry (←mkEq e mapM) false)
    
    -- -- TODO: I am guessing this is... slow?
    -- let consMapM ← mapM.runTactic (←`(tactic| rw[$(mkIdent ``Vector.mapM_mk_singleton_append):ident]))
    -- -- TODO: Puh-ROOF!
    -- return .step consMapM (←mkSorry (←mkEq e mapM) false)

-- def _root_.Vector.mapM_mk_eq_append' : Sym.Simp.Simproc := fun e ↦ do
--   let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .rfl
--   let_expr _root_.Vector.mk _ sz arr _ := vec | return .rfl
--   unless arr.isAppOf ``List.toArray || arr.isAppOf ``Array.mk do return .rfl
--   let l ← arr.getAppArgs[1]?.getDM (unreachable!)
--   let_expr List.cons t hd tl := l | return .rfl
--   _

/--
`Vector.mapM_mk_singleton_append` is a part of `Vector.mapM_mk_append` to ensure that
the transformation `#v[a, b] ==> #v[a] ++ #v[b]` does not get undone by `Vector.mk_append_mk`.
-/
def mapM : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mapM_mk_cons, ``Vector.mapM_mk_empty,

    ``Compiler.explodeVectorMapM
  ]

-- def mapM_test : MetaM Methods :=
--   mkPostMethods #[
--     ``Vector.mapM_mk_cons, ``Compiler.explodeVectorMapM
--   ]

def zipWith : MetaM Methods :=
  mkPostMethods #[
    ``Vector.mk_zipWith_mk, ``List.zipWith_toArray,
    
    ``List.zipWith_cons_cons, ``List.zipWith_nil_left, ``List.zipWith_nil_right,

    ``Compiler.explodeVectorZipWith
  ]

end Vector

end

end SymSets

def compileExample (ex : Name) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Format := do
  compile (((←getEnv).find? ex).get!.value!) simpset >>= (liftM ∘ PrettyPrinter.ppExpr)

def compileJustSym (e : Expr) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Format := do
  lambdaTelescope e fun args e ↦ do
    let compiled ← Compiler.Simp.simplify (simpset ∪ (←SymSets.General.compilerSet)) e
    logInfo m!"Compiled: {compiled}"
    Sym.mkLambdaFVarsS args compiled >>= (liftM ∘ PrettyPrinter.ppExpr)

def compileExampleJustSym (ex : Name) (simpset : Sym.Simp.Methods) : Sym.Simp.SimpM Format := do
  let e := ((←getEnv).find? ex).get!.value!
  compileJustSym e simpset

open SymSets in
elab "compile_just_sym" "[" simps:ident,* "]" : tactic => do
  let simps ← simps.getElems.mapM fun s ↦ realizeGlobalConstNoOverload s.raw
  let methods ← simps.mapM (liftM ∘ Simp.API.getMethodsM)
  let methods ← liftM <| methods.foldl (fun method acc ↦ method ∪ acc) (pure {})
  Tactic.liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

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

def ex₁ (_vec : Vector Nat 3) : Option Unit := do
  eq0 #v[4, 5][0]

set_option profiler true
set_option profiler.threshold 10

-- `e` : Vector (3 + 3)
-- `Eq.mp (3 + 3 = 6) e` : Vector 6
-- 

-- /-- info: fun _vec => eq0 4 -/
-- #guard_msgs in
#eval spoon <| do compileExampleJustSym ``ex₁ (←getElem)
-- set_option trace.Clap.Compile true

def ex₂ (vec : Vector Nat 3) : Option Unit := do
  let x := (vec ++ vec)[0] -- `GetElem (Vector _ (3 + 3))`
  eq0 x

example {vec : Vector Nat 3} : ex₂ vec = sorry := by
  unfold ex₂



/-- info: fun vec => eq0 vec[0] -/
#guard_msgs in
#eval spoon <| do compileExampleJustSym ``ex₂ (←(append ∪ zeta ∪ getElem))

def ex₃ (vec : Vector Nat 200) : Option Unit := do
  let x := vec.map (·+1)
  eq0 x[0]

-- -- set_option maxRecDepth 1000
-- /-- info: fun vec => eq0 (vec[0] + 1) -/
-- #guard_msgs in
-- #eval spoon <| do compileExampleJustSym ``ex₃ (←(map ∪ zeta ∪ getElem))

def ex₄ (vec : Vector Nat 150) : Option Unit := do
  let x ← vec.mapM (fun x ↦ return x + 1)
  eq0 x[0]
-- set_option trace.Clap.Compile true

set_option profiler true
-- set_option trace.sym.issues true
-- /-- info: fun vec => eq0 (vec[0] + 1) -/

set_option debug.skipKernelTC true
-- set_option trace.Clap.Compile.debug.simp true
set_option pp.exprSizes true
-- set_option debug.skipKernelTC true in

-- cache [0x1 ↦ id x]
-- e₁ := (fun y ↦ f (id y) (id x)) x
-- beta
-- e₂ := f (id x) (0x1)
-- share [e₃ := share e₂]
-- e₃ := f 0x1 0x1
-- lemma : f ?x ?x ==> 42
-- 42

-- set_option trace.Clap.Compile true in
--  20 -   .1s |  .1 | 0   | simproc:  
--  30 -   .2s |  .1 |  .1 | simproc: 
--  40 -   .3s |  .2 |  .1 | simproc: 
--  50 -   .5s |  .4 |  .2 | simproc: 
--  60 -   .9s |  .4 |  .2 | simproc: 
--  70 -  1.3s |  .6 |  .2 | simproc: 
--  80 -  1.9s |  .5 |  .1 | simproc:  .3s
--  90 -  2.4s |  .5 |  .1 | simproc:  .3s
-- 100 -  3.5s | 1.0 |  .5 | simproc:  .4s
-- 110 -  4.3s | 0.9 |  .5 | simproc:  .5s
-- 120 -  5.7s | 1.4 |  .9 | simproc:  .6s
-- 130 -  8.0s | 2.3 |  .2 | simproc:  .8s
-- 140 - 10.5s | 2.5 |  .0 | simproc:  .9s
-- 150 - 13.0s | 2.5 |  .0 | simproc: 1.1s
-- 160 - 15.4s |     |     | simproc: 1.3s

set_option trace.sym.issues true in
set_option trace.Clap.Compile true in
#eval spoon <| do compileExampleJustSym ``ex₄ (←(mapM))


#check Vector.mapM_mk_empty

-- #eval spoon <| do compileExampleJustSym ``ex₄ (←(mapM_test))
  
example {vec : Vector Nat 20} : ex₄ vec = sorry := by
  unfold ex₄
  -- compile_just_sym []
  compile_just_sym [ground, SymSets.Vector.mapM, SymSets.Vector.getElem, compilerSet]
  rw [List.getElem_toArray]
  simp
  -- simp only [Option.bind_some]

  compile_just_sym [compilerSet]

def ex₅ (vec : Vector Nat 3) : Option Unit := do
  eq0 ((vec ++ vec)[0])
  eq0 0
  let res := vec.zipWith (bs := vec.map (·+1)) fun x y ↦ x + y
  eq0 res[0]
  eq0 res[1]
  eq0 res[2]

example {vec : Vector Nat 3} : ex₅ vec = sorry := by
  unfold ex₅
  compile_just_sym [
    SymSets.Vector.append,
    SymSets.Vector.getElem,
    SymSets.Vector.zipWith,
    SymSets.Vector.map,
    compilerSet,
    zeta
  ]

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

-- set_option trace.Clap.Compile true

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
