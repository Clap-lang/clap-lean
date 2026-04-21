import Lean
import Qq

import Clap.Compiler.Simp
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

def _root_.Lean.Meta.lambdaTelescopeOne!.{u}
  {n : Type → Type u} [MonadControlT MetaM n] [Monad n]
  {α : Type} [Inhabited (n α)]
  (e : Expr) (k : Expr → Expr → n α) (cleanupAnnotations : Bool := false) : n α :=
  lambdaTelescope (cleanupAnnotations := cleanupAnnotations) e fun args body ↦ do
    let #[arg] := args | panic! "Expected a single argument. Got: {args.size}"
    k arg body

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
      trace[Clap.Compile.simp] "[↓] {checkEmoji}\n{todo}\n--->\n{simped}"
      trace[Clap.Compile.down] "\ngo [↓]:\n{simped}"
      down reduce reduceOuter stack simped
    else
      trace[Clap.Compile.simp] "[↓] {crossEmoji}\n{todo}"
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

         let simped ← reduceOuter bind
         if simped != bind
         then trace[Clap.Compile.simp] "[↑] {checkEmoji}\n{bind}\n--->\n{simped}"
         else trace[Clap.Compile.simp] "[↑] {crossEmoji}\n{bind}"

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
    m!"Compiler: [only := {false}, singlePass := {false}, set := {repr compilerSet} ∪ {repr simpset}"
    
  down (Simp.simplify (only := only) (singlePass := true) simpset)
       (Simp.simplify (only := false) (singlePass := false) (compilerSet.union simpset)) [] e
  where
    compilerSet : SimpSet :=
      SimpSet.withAllPost #[``Option.bind_assoc, ``bind_assoc] #[``Option.bind_eq_bind]

namespace Exampru

opaque eq0 (e : Nat) : Option Unit

def ex₀ : Expr := q(
  do eq0 0
     eq0 1
     let res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 2)
     eq0 3
     return ()
)                    

/--
info: do
  eq0 0
  eq0 1
  do
    eq0 2
    let init ← eq0 2
    pure init
  eq0 3
  pure ()
-/
#guard_msgs in
#eval compile ex₀
  (SimpSet.withAllPost #[``List.foldlM_cons, ``List.foldlM_nil]) >>=
  (liftM ∘ PrettyPrinter.ppExpr)

end Exampru

end Clap.Compiler
