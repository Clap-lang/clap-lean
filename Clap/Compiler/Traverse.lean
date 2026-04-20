import Lean
import Qq

import Clap.Compiler.Simp
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean Meta Qq Elab

abbrev ExprS := Sum Expr Expr

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
  if !(←e.isBind) then return .none
  let firstExplicitArg := (←getFunInfo e.getAppFn).paramInfo.findIdx (·.binderInfo.isExplicit)
  let args := e.getAppArgs
  return (args[firstExplicitArg]!, args[firstExplicitArg + 1]!)

def _root_.Lean.Expr.mkBind (l r : Expr) (m? : Name := ``Bind.bind) : MetaM Expr :=
  mkAppM m? #[l, r]

private def treeEmoji : String := "🌲"

mutual

private partial def down (todo : Expr) (stack : List ExprS) : TermElabM Expr := do
  if let .some (l, r) ← todo.getBindArgs?
  then
    trace[Clap.Compile.down] "\npush [→]:\n{r}\ngo [↓]:\n{l}"
    down l (.inr r :: stack)
  else
    let simped ← Simp.simplify `dbgSimp todo
    trace[Clap.Compile.simp] "\n{todo}\n--->\n{simped}"
    if simped != todo
    then
      trace[Clap.Compile.down] "\n{checkEmoji} go [↓]:\n{simped}"
      down simped stack
    else
      trace[Clap.Compile.down] "\n{crossEmoji} go [↑]:\n{todo}"
      up todo stack

private partial def up (done : Expr) (stack : List ExprS) : TermElabM Expr := do
  match stack with
  | [] =>
    trace[Clap.Compile.up] "Done"
    return done
  | .inr r :: stack =>
    trace[Clap.Compile.up] "\npush [←]:\n{done}\ngo [↓]:\n{r}"
    down r (.inl done :: stack)
  | .inl l :: stack => do
    trace[Clap.Compile.up] "\ngo [↑]:\n{l}\n>>=\n{done}"
    up (←Expr.mkBind l done) stack

end

def compile (e : Expr) : TermElabM Expr := do
  withTraceNode `Clap.Compile formatExprWith do
  down e []

namespace Exampru

opaque eq0 (e : Unit) : Option Unit

def ex₀ : Expr := q(
  do eq0 ()
     eq0 ()
     let res ← (do eq0 (); eq0 ())
     eq0 res
     return ()
)

attribute [dbgSimp] Option.bind_eq_bind

-- set_option trace.Clap.Compile true

/--
info: do
  eq0 ()
  (eq0 ()).bind fun x => ((eq0 ()).bind fun x => eq0 ()).bind fun res => (eq0 res).bind fun x => pure ()
-/
#guard_msgs in
#eval compile ex₀ >>= (liftM ∘ PrettyPrinter.ppExpr)

end Exampru

end Clap.Compiler
