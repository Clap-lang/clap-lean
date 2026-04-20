import Lean
import Qq

namespace Clap.Compiler

open Lean Meta Qq

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

mutual

private partial def down (todo : Expr) (stack : List ExprS) : MetaM Expr := do
  if let .some (l, r) ← todo.getBindArgs?
  then
    down l (.inr r :: stack)
  else
    let simped := id todo
    if simped != todo
    then down simped stack
    else up todo stack

private partial def up (done : Expr) (stack : List ExprS) : MetaM Expr :=
  match stack with
  | [] => return done
  | .inr r :: rest => down r (.inl done :: rest)
  | .inl l :: rest => do up (←Expr.mkBind l done) rest

end

def compile (e : Expr) : MetaM Expr := down e []

namespace Exampru

opaque eq0 (e : Unit) : Option Unit

def ex₀ : Expr := q(
  do eq0 ()
     eq0 ()
     let res ← (do eq0 (); eq0 ())
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
      eq0 ()
  eq0 res
  pure ()
-/
#guard_msgs in
#eval compile ex₀ >>= PrettyPrinter.ppExpr

end Exampru

end Clap.Compiler
