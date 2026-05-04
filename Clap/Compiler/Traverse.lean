import Lean
import Qq

import Clap.Compiler.Simp
import Clap.Compiler.Vectors
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean Meta Qq Elab

abbrev ExprS := Expr × Expr ⊕ Expr

def ExprS.pretty (e : ExprS) : MetaM String := do
  match e with
  | .inl (e, binder) => return s!"λ {binder} ↦ {←PrettyPrinter.ppExpr e}"
  | .inr e => PrettyPrinter.ppExpr e <&> Format.pretty

def _root_.Lean.Expr.isBind (e : Expr) : MetaM Bool := do
  return e.isAppOf ``Bind.bind || e.isAppOf ``Option.bind

def _root_.Lean.Expr.getBindArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  -- If `e` is not `λ _ ↦ _`, then `lambdaTelescope = id`.
  lambdaTelescope e fun _ e ↦ do
    if !(←e.isBind) then return .none
    let firstExplicitArg := (←getFunInfo e.getAppFn).paramInfo.findIdx (·.binderInfo.isExplicit)
    let bindArgs := e.getAppArgs
    return .some (
      bindArgs[firstExplicitArg]!,
      bindArgs[firstExplicitArg + 1]!
    )

def _root_.Lean.Expr.mkBind (l r : Expr) (m? : Name := ``Bind.bind) : MetaM Expr := do
  mkAppM m? #[l, r]

private def treeEmoji : String := "🌲"

mutual

private partial def down (reduce : Expr → TermElabM Expr)
                         (reduceOuter : Expr → TermElabM Expr)
                         (stack : List ExprS) (todo : Expr) : TermElabM Expr := do
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
      up reduce reduceOuter stack todo

private partial def up (reduce : Expr → TermElabM Expr)
                       (reduceOuter : Expr → TermElabM Expr)
                       (stack : List ExprS) (done : Expr) : TermElabM Expr := do
  match stack with
  | [] =>
    trace[Clap.Compile.up] "Done"
    return done
  | .inr r :: stack =>
    lambdaTelescopeOne! r fun arg body ↦ do
      trace[Clap.Compile.up] "\npush [←]:\n{(done, arg)}\ngo [↓]:\n{body}"
      down reduce reduceOuter (.inl (done, arg) :: stack) body
  | .inl l :: stack => do
    let bind ← mkBindWith l done
    let up := up reduce reduceOuter stack
    if ← isDefEq (←inferType l.2) q(Unit)
    then trace[Clap.Compile.up] "\ngo [↑]:\n{bind}"
         up bind
    else trace[Clap.Compile.simp] "Binding value: {l.2}"
         trace[Clap.Compile.simp] "REMOVE ME:\n{bind}"
         trace[Clap.Compile.simp] "stack:\n{stack.length}"
         let simped ← reduceOuter bind
         if simped != bind
         then trace[Clap.Compile.simp] "[↑] {checkEmoji}\n{bind}\n==>\n{simped}"
         else trace[Clap.Compile.simp.fail] "[↑] {crossEmoji}\n{bind}"

         trace[Clap.Compile.up] "\ngo [↑]:\n{simped}"
         up simped
  where mkBindWith (stackEntry : Expr × Expr) (cont : Expr)
                   (m? : Name := ``Bind.bind) : MetaM Expr := do
    mkLambdaFVars #[stackEntry.2] cont >>= stackEntry.1.mkBind (m? := m?)

end

open Simp API

def compile (e : Expr) (simpset : SimpSet) (only : Bool := true) : TermElabM Expr := do
  withTraceNode `Clap.Compile formatExprWith do
  trace[Clap.Compile.simp.config]
    m!"Reducer: [only := {only}, singlePass := {true}, set := {repr simpset}"
  trace[Clap.Compile.simp.config]
    m!"Compiler: [only := true, singlePass := {false}, set := {repr compilerSet} ∪ {repr simpset}"
  
  lambdaTelescope e fun args e ↦ do
    let compiled ←
      down (simplify (only := only) (singlePass := true) simpset)
           (simplify (only := true) (singlePass := true) (compilerSet ∪ simpset)) [] e
    mkLambdaFVars args compiled
  where
    compilerSet : SimpSet :=
      SimpSet.withAllPost #[
        ``Option.bind_assoc, ``bind_assoc,
        ``Option.pure_def,
        ``Option.bind_eq_bind, ``Option.bind_fun_some, ``Option.bind_some, ``bind_pure, ``pure_bind,
        ``Option.map_eq_map, ``Option.map_some
      ]

namespace CompileSets

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

set_option autoImplicit true in
@[simp, grind =] theorem getElem!_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) :
    c[i]! = c[i]'(sorry) := by sorry

def getElem! : SimpSet :=
  SimpSet.withAllPost #[
    ``getElem!_pos
  ] ∪ getElem

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

dsimproc_decl rwMk_append_mk (Vector.mk _ _ ++ Vector.mk _ _) := fun e ↦ do
  let x ← e.runTactic (←`(tactic| rw [$(mkIdent ``Vector.mk_append_mk):ident]))
  return .visit x

def append : SimpSet :=
  SimpSet.withAllPost #[
    ``rwMk_append_mk, ``List.append_toArray, -- ``Vector.mk_append_mk

    ``List.cons_append, ``List.nil_append
  ]

def take : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.take_mk, ``List.take_toArray,

    ``List.take_succ_cons, ``List.take_nil
    -- ``List.take_cons, ``List.take_nil
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

    -- ``List.drop_cons, ``List.drop_nil,
    ``List.drop_succ_cons, ``List.drop_zero, ``List.drop_nil
  ]

def foldl : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.foldl_mk, ``List.foldl_toArray,

    ``List.foldl_cons, ``List.foldl_nil
  ]

def foldr : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.foldr_mk, ``List.foldr_toArray,

    ``List.foldr_cons, ``List.foldr_nil
  ]

def sum : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.sum_eq_foldr
  ] ∪ foldr
#check map_bind
-- example {l : Vector Nat 2} :
--   (do let l ← (((fun x => #v[x]) <$> some 1).bind fun a => some #v[a[0]])
--       some #v[l[0]]) = sorry := by
--   rw [Option.map_eq_map]
--   rw [Option.map_some] -- map_pure | map_pure
--   done

-- opaque share : Nat → Nat

-- example {inputs : Vector Nat 2} : Option.map (fun x => #v[x])
--           ((some
--                 (share
--                   ((inputs[1] + 2) *
--                     (inputs[1] + 2)))).bind
--             fun a =>
--             (some (share (a * a))).bind fun a =>
--               some (a * (inputs[1] + 2))) = sorry := by
--   simp?
--   done

-- example {inputs : Vector Nat 2}: (Option.map (fun x => #v[x]) do
--           let x2 ←
--             some
--                 (share
--                   ((inputs[1] + 2) *
--                     (inputs[1] + 2)))
--           let x4 ← some (share (x2 * x2))
--           some (x4 * (inputs[1] + 2))) = sorry := by
--   simp?
--   done

-- @[simp]
-- theorem _root_.Vector.mapM_singleton {α β} {m} [Monad m] [LawfulMonad m] {f : α → m β} {x} :
--   #v[x].mapM f = (#v[·]) <$> f x := by
--   apply Vector.map_toArray_inj.mp; simp

@[simp]
theorem _root_.Vector.mapM_singleton {α β} {m} [Monad m] [LawfulMonad m] {f : α → m β} {x} :
  #v[x].mapM f = f x >>= (pure #v[·]) := by
  apply Vector.map_toArray_inj.mp; simp

@[simp↓ high]
theorem _root_.Vector.mapM_mk_singleton_append {m} [Monad m] [LawfulMonad m] {α β} {n} {f : α → m β}
  (v : Vector α n) {x : α} :
  (#v[x] ++ v).mapM f = (return #v[(←f x)] ++ (←v.mapM f)) := by simp

def liftTermElabM {α} (m : TermElabM α) : SimpM α := liftM m.run'

/--
0. Only for `Vector.mapM f xs`.
1. Vector.mapM f #v[a, b, c] → Vector.mapM f (#v[a] ++ #v[b, c])
2. Vector.mapM f (#v[x] ++ v) = do
     let __do_lift ← f x
     let __do_lift_1 ← Vector.mapM f v
     pure (#v[__do_lift] ++ __do_lift_1)
-/
dsimproc_decl _root_.Vector.mapM_mk_eq_append (_root_.Vector.mapM _ _) := fun e ↦ do
  let_expr _root_.Vector.mapM _ _ _ _ _ f vec := e | return .continue
  let_expr _root_.Vector.mk _ sz arr _ := vec | return .continue
  let_expr List.toArray _ l := arr | return .continue
  let_expr List.cons t hd tl := l | return .continue
  let szN := (←simp sz).expr.nat?.get!
  if szN <= 1 then return .continue
  let hd ← liftTermElabM (mkVecLit (←mkListLit t [hd]) (mkNatLit 1))
  let tl ← liftTermElabM (mkVecLit tl (toExpr (szN - 1)))
  let consHdTl ← mkAppM ``HAppend.hAppend #[hd, tl]
  let mapM ← mkAppM ``_root_.Vector.mapM #[f, consHdTl]  
  let consMapM ← mapM.runTactic (←`(tactic| rw[$(mkIdent ``Vector.mapM_mk_singleton_append):ident]))
  return .visit consMapM

def mapM : SimpSet :=
  SimpSet.withAllPost #[
    ``Vector.mapM_mk_singleton_append,
    
    ``Vector.mapM_mk_eq_append, ``Vector.mapM_singleton

    -- ``map_pure, ``Option.map_eq_map, ``Option.map_some, ``Option.bind_eq_bind
  ] ∪ append ∪ getElem

end Vector

end CompileSets

namespace Exampru

def compileExample (ex : Name) (simpset : SimpSet) (only : Bool := true) : TermElabM Format := do
  compile (((←getEnv).find? ex).get!.value!) simpset only >>= (liftM ∘ PrettyPrinter.ppExpr)

def eq0 (e : Nat) : Option Unit := .some ()

def ex₀ : Expr := q(
  do eq0 0
     eq0 1
     let _res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 2)
     eq0 3
     return ()
)                    

-- /--
-- info: do
--   eq0 0
--   eq0 1
--   do
--     eq0 2
--     let init ← eq0 2
--     pure init
--   eq0 3
--   pure ()
-- -/
-- #guard_msgs in
-- #eval compile ex₀
--   (SimpSet.withAllPost #[``List.foldlM_cons, ``List.foldlM_nil]) >>=
--   (liftM ∘ PrettyPrinter.ppExpr)

-- def ex₁ (n : Nat) : Option Unit := do
--   eq0 0
--   let res ← (#v[0, 1].foldlM (fun acc _ ↦ return acc) #v[n, 6])
--   let res' := res.map (·+1)
--   eq0 (res'[0])
--   eq0 (res'[1])
--   return ()

open CompileSets Vector

-- /--
-- info: fun n => do
--   eq0 0
--   (eq0 (n + 1)).bind fun a => (eq0 7).bind fun a => some ()
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₁
--         (foldlM ∪ getElem ∪ map ∪ explode)

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

-- def ex₄ (vec : Vector Nat 3) : Option Unit := do
--   eq0 ((vec ++ vec)[0])
--   eq0 0
--   let res := vec.zipWith (bs := vec.map (·+1)) fun x y ↦ x + y
--   eq0 res[0]
--   eq0 res[1]
--   eq0 res[2]

-- /--
-- info: fun vec => do
--   eq0 vec[0]
--   eq0 0
--   eq0 (2 * vec[0] + 1)
--   eq0 (2 * vec[1] + 1)
--   eq0 (2 * vec[2] + 1)
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₄
--         (foldlM ∪ getElem ∪ map ∪ explode ∪ append ∪ mapIdx ∪ zipWith)
  
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
-- -- set_option trace.Clap.Compile true
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

-- /--
-- info: fun vec => do
--   eq0 42
--   (eq0 (vec[0] + 2)).bind fun a => (eq0 (vec[1] + 6)).bind fun a => eq0 (vec[2] + 11)
-- -/
-- #guard_msgs in
-- #eval compileExample ``ex₇ (explode ∪ mapM ∪ zipWith)

-- Vector.mapM sigma
--       #v[(Vector.mapIdx (fun i s => s + Constant.C.C03[i]) (#v[0] ++ #v[inputs[0], inputs[1]]))[0],
--         (Vector.mapIdx (fun i s => s + Constant.C.C03[i]) (#v[0] ++ #v[inputs[0], inputs[1]]))[1],
--         (Vector.mapIdx (fun i s => s + Constant.C.C03[i]) (#v[0] ++ #v[inputs[0], inputs[1]]))[2]] 



-- def const : Nat := 42

-- def ex₃ (vec : Vector Nat 3) : Option Unit := do
--   eq0 ((vec ++ vec)[0])
--   eq0 0
--   let res := vec.mapIdx fun i _ ↦ i
--   eq0 res[0]
--   eq0 res[1]
--   eq0 res[2]


    -- ``Vector.mapM_mk_eq_append, ``Vector.mapM_singleton, ``map_pure
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

-- #eval compileExample ``ex₃ (mapIdx ∪ append ∪ getElem ∪ explode)
-- example {vec : Vector Nat 3} :
--   #v[0] ++ #v[vec[0], vec[1], vec[2]] = sorry := by
--   -- rw [Vector.mk_append_mk]
--   simp [Vector.mk_append_mk]
-- def ex₈ (vec : Vector Nat 3) : Option Unit := do
--   let res := (#v[0] ++ vec).mapIdx (fun i s => s + const)
--   eq0 res[0]
-- set_option trace.Clap.Compile true
-- #check Vector.mk_append_mk
-- #eval compileExample ``ex₈ (
--      append ∪
--      CompileSets.Vector.foldlM ∪
--      CompileSets.Vector.mapIdx ∪
--      CompileSets.Vector.map ∪
--      CompileSets.Nat.arith ∪
--      CompileSets.Array.range ∪
--      CompileSets.List.range ∪
--      CompileSets.Logic.cases ∪ 
--      CompileSets.Vector.getElem! ∪
--      CompileSets.Vector.explode)

end Exampru

end Clap.Compiler
