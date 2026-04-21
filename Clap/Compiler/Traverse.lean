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

/--
TODO: We will probably remove the old compiler.
This is `isBind`.
-/
def _root_.Lean.Expr.isBind (e : Expr) : MetaM Bool :=
  isDefEq e.getAppFn (.const ``Bind.bind [0, 0])

/--
TODO: We will probably remove the old compiler.
This is based on `getBindArgs!`.
-/
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

def mkBindWith (stackEntry : Expr × Expr) (cont : Expr) (m? : Name := ``Bind.bind) : MetaM Expr := do
  mkLambdaFVars #[stackEntry.2] cont >>= stackEntry.1.mkBind (m? := m?)

private def treeEmoji : String := "🌲"

mutual

private partial def down (reduce : Expr → TermElabM Expr)
                         (todo : Expr) (stack : List ExprS) : TermElabM Expr := do
  if let .some (l, r) ← todo.getBindArgs?
  then
    trace[Clap.Compile.down] "\npush [→]:\n{r}\ngo [↓]:\n{l}"
    down reduce l (.inr r :: stack)
  else
    let simped ← reduce todo
    trace[Clap.Compile.simp] "\n{todo}\n--->\n{simped}"
    if simped != todo
    then
      trace[Clap.Compile.down] "\n{checkEmoji} go [↓]:\n{simped}"
      down reduce simped stack
    else
      trace[Clap.Compile.down] "\n{crossEmoji} go [↑]:\n{todo}"
      up reduce todo stack 

private partial def up (reduce : Expr → TermElabM Expr)
                       (done : Expr) (stack : List ExprS) : TermElabM Expr := do
  match stack with
  | [] =>
    trace[Clap.Compile.up] "Done"
    return done
  | .inr r :: stack =>
    lambdaTelescopeOne! r fun arg body ↦ do
      trace[Clap.Compile.up] "\npush [←]:\n{(done, arg)}\ngo [↓]:\n{body}"
      down reduce body (.inl (done, arg) :: stack)
  | .inl l :: stack => do
    let bind ← mkBindWith l done
    trace[Clap.Compile.up] "\ngo [↑]:\n{l}\n>>=\n{bind}"
    up reduce bind stack

end

def compile (e : Expr) (simpset : Name := `simpAll) : TermElabM Expr := do
  withTraceNode `Clap.Compile formatExprWith do
  down (Simp.simplify simpset) e []

namespace Exampru

opaque eq0 (e : Unit) : Option Unit

def ex₀ : Expr := q(
  do eq0 ()
     eq0 ()
     let res ← ([0, 1].foldlM (init := ()) fun _ _ ↦ eq0 ())
     eq0 res
     return ()
)                    

/--
info: do
  eq0 ()
  eq0 ()
  let res ←
    do
      eq0 ()
      let init ← eq0 ()
      some init
  eq0 res
  some ()
-/
#guard_msgs in
#eval compile ex₀ >>= (liftM ∘ PrettyPrinter.ppExpr)

end Exampru

end Clap.Compiler
