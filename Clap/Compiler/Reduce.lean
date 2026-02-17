import Lean
import Qq
import Mathlib.Tactic
import Mathlib.Lean.Meta
import Clap.Spec

open Lean Qq Meta

namespace Clap

#check isRecursiveDefinition

-- def unfoldAnyStep (e : Expr) : MetaM TransformStep := do
--   let .const name _ := e.getAppFn | return .continue
--   if let .some name ← Meta.getUnfoldEqnFor? name
--   then logInfo m!"{e} has an unfold def called {name}"
--        let r ← unfold e name
--        return .continue r.expr
--   else let some v ← unfoldDefinition? e | return .continue
--        return .visit v

-- def unfoldAnyStep (e : Expr) : MetaM TransformStep := do
--   if (←Meta.isTypeFormer e) then return .continue
--   if let some v ← unfoldDefinition? e
--   then return .visit v
--   else let .some name ← Meta.getUnfoldEqnFor? (e.getAppFn.constName?.getD default) | return .continue
--        if name.getRoot != `Clap then return .continue
--        logInfo m!"name: {name}"
--        let r ← unfold e (e.getAppFn.constName!)
--        logInfo m!"r: {r.expr}"
--        return .continue 

def isNameFormer (e : Expr) (typeName : Name) : MetaM Bool :=
  forallTelescopeReducing e fun _ ret ↦ return ret.isAppOf typeName

def isPrivileged (e : Expr) : MetaM Bool := do
  return (←Meta.isTypeFormer e) || /-Probably wrong.-/ e.isAppOf ``Bind.bind ||
         (←Meta.inferType e).isAppOf ``Monad || (←Meta.inferType e).isAppOf ``Bind ||
         (←isNameFormer (←Meta.inferType e) ``Bind) || (←isNameFormer (←Meta.inferType e) ``Monad)

def unfoldAnyStep (e : Expr) : MetaM TransformStep := do
  if ←isPrivileged e then return .continue
  let some v ← unfoldDefinition? e | return .continue
  return .visit v

def unfoldAny (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := unfoldAnyStep)

def forceUnfold (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget unfoldAny >>= MVarId.transformTarget (f := liftM ∘ Core.betaReduce)

def foldProjs (e : Expr) : MetaM Expr := do
  if (e.find? (·.isProj)).isNone then return e
  let post (e : Expr) := do
    if ←isPrivileged e then return .continue
    let .proj structName idx s := e | return .done e
    let some info := getStructureInfo? (←getEnv) structName | return .done e
    if h : idx < info.fieldNames.size then
      let fieldName := info.fieldNames[idx]
      return .visit (← withDefault <| mkProjection s fieldName)
    else
      return .done e
  Meta.transform e (post := post)

def zetaHaveStep (e : Expr) : MetaM TransformStep := do
  if ←isPrivileged e then return .continue
  let .letE _ _ v b _ := e | return .continue
  -- logInfo m!"v: {v} b: {b} e: {e} | Expand: {Meta.expandLet b #[v]}"
  return .visit <| Meta.expandLet b #[v]
  -- if e.isHave
  -- then logInfo m!"Telescoping: {e}"
  --      letTelescope e fun args body ↦ do
  --        let #[arg] := args | throwError "let expressions must bind a single value"
  --        logInfo m!"args: {args} e: {e} e.val: {e.letValue!} body: {body}"
  --        let subst := FVarSubst.empty.insert arg.fvarId! e.letValue!
  --        return .visit (subst.apply body)
  -- else return .continue

def zetaHave (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := zetaHaveStep)

def reduceExpr (e : Expr) : MetaM Expr := do -- >>= reduce
  zetaHave e >>= unfoldAny >>= foldProjs >>= (Core.betaReduce ·)

open MVarId in
def _root_.Lean.MVarId.reduceTarget (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget (f := reduceExpr)

open Elab Tactic in
elab "test_reduce" : tactic => do
  liftMetaTactic' MVarId.reduceTarget

-- def ex₀ {p : Nat} [Fact (Nat.Prime p)] (x y : ZMod p) : Option Unit := do
--   Clap.Spec.Compiler.eq0 (x + y)
--   Clap.Spec.Compiler.eq0 (y + x)
--   Clap.Spec.Compiler.accept

-- example {x y} : ex₀ (p := 2) x y = Option.some () := by
--   unfold ex₀
--   test_reduce

def produceEq0 {p} (l : List (ZMod p)) : Option Unit :=
  match l with
  | [] => .some ()
  | hd :: tl => do
    Clap.Spec.Compiler.eq0 hd
    produceEq0 tl

def x {p : Nat} [Fact (Nat.Prime p)] (x : ZMod p) : Option Unit := do
  let y := id (x + 2)
  let myList := [(1 : ZMod p), 2, y].map (·+1)
  produceEq0 myList
  .some Clap.Spec.Compiler.accept

example : x (p := 2) = sorry := by
  unfold x
  
  test_reduce
  sorry
  
  -- unfold produceEq0
  -- unfold produceEq0
  -- unfold produceEq0
  
--   done

end Clap
