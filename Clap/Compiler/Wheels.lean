import Lean

initialize Lean.registerTraceClass `Clap.Compiler

/--
`Clap.Compiler.preprocess` reports prime resolution and typeclass instantiation.
-/
initialize Lean.registerTraceClass `Clap.Compiler.preprocess (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.nameResolution (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.numIters (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.unfoldAny (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.dsimp (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.beta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.zeta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.linearise (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.foldProjs (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.letSome (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.serialise (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.curry (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile

initialize Lean.registerTraceClass `Clap.Compile.traversal (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.down (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.up (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.config (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.kaboom (inherited := true)

open Lean Elab.Term in
def formatExprWith {m : Type _ → Type _} [Monad m]
                   (s : String := "") (res : Except Exception Expr) : m MessageData :=
  return m!"{s}\n{match res with | .error _ => "" | .ok res => res}"

open Lean Meta in
def Lean.Meta.lambdaTelescopeOne!.{u}
  {n : Type → Type u} [MonadControlT MetaM n] [Monad n]
  {α : Type} [Inhabited (n α)]
  (e : Expr) (k : Expr → Expr → n α) (cleanupAnnotations : Bool := false) : n α :=
  lambdaTelescope (cleanupAnnotations := cleanupAnnotations) e fun args body ↦ do
    let #[arg] := args | panic! s!"Expected a single argument. Got: {args.size}"
    k arg body

open Lean Meta in
def Lean.Meta.forallTelescopeOne!.{u}
  {n : Type → Type u} [MonadControlT MetaM n] [Monad n]
  {α : Type} [Inhabited (n α)]
  (e : Expr) (k : Expr → Expr → n α) (cleanupAnnotations : Bool := false) : n α :=
  forallTelescope (cleanupAnnotations := cleanupAnnotations) e fun args body ↦ do
    let #[arg] := args | panic! s!"Expected a single argument. Got: {args.size}"
    k arg body

register_simp_attr dbgSimp

register_simp_attr compilerSimp
