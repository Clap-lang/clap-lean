import Lean

open Lean

initialize registerTraceClass `Clap.Compile

initialize registerTraceClass `Clap.Compile.simp (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.kaboom (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.getElem_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.mk_append_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_mapM_mk_eq_append (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.sequenceAsVecExpr (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.zeta (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.evalGround (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_getElem_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_mk_zipWith_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_mapM_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_mapIdx_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_mk_append_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.vector_set_mk (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.mapM_mk_single (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.monad (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.monad.bind_assoc (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.monad.bind_eq_bind (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.monad.bind_some (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.monad.pure_apply (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.monad.top_level (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.preprocess (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.flattenBinds (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.bindPureMany (inherited := true)

initialize registerTraceClass `Clap.Compile.simp.proc.seemsTotallySafeInDTT (inherited := true)

initialize registerTraceClass `Clap.Compile.debug.simp (inherited := true)

/-
TODO: Having a `dbg` option and a `trace dbg` option is silly.
That said, I want to treat a `traceClass` as a trace class only, I don't want
to check it programatically whether it's on, to use as a debug flag as well.
-/
initialize Lean.registerTraceClass `Clap.Compile.dbg (inherited := false)

register_option Clap.traversalDbg : Bool := {
  defValue := false
  descr := "debugging info for traversal"
}

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

open Lean Meta Sym Elab in
def Lean.Meta.Sym.Simp.liftTermElabM {α} (m : TermElabM α) : Sym.Simp.SimpM α := liftM m.run'

section

open Lean.Meta

private def evalGround : Sym.Simp.Simproc := fun e ↦ do
  let e' ← Sym.Simp.evalGround {} e
  unless Sym.isSameExpr e (e'.getResultExpr e) do
    trace[Clap.Compile.simp.proc.evalGround]
      m!"\n{e}\n==>\n{e'.getResultExpr e}"
  return e'

def Clap.SymSets.General.ground : MetaM Sym.Simp.Methods := do
  return {
    post := evalGround
  }

def Lean.Meta.Sym.simpWithGround (e : Expr) : SymM Sym.Simp.Result :=
  Clap.SymSets.General.ground >>= (Sym.simp e ·)

end

def Clap.Dbg.timeInSecondsOfMs (begin «end» : Nat) : Float :=
  (Float.ofNat «end» - Float.ofNat begin) / Float.ofNat 1000

def Clap.Dbg.timeSince (begin : Nat) (msg := ""): Lean.Meta.Sym.Simp.SimpM Unit := do
  Lean.logWarning m!"{msg}\n{(Float.ofNat (←IO.monoMsNow) - Float.ofNat begin) / Float.ofNat 1000}s"

open Lean Meta Sym in
def Clap.Dbg.timeS {α} {m : Type _ → Type _} [Monad m] [MonadLiftT BaseIO m] (k : m α) : m (α × Float) := do
  let s ← IO.monoNanosNow
  let a ← k
  let e ← IO.monoNanosNow
  return (a, (e - s).toFloat / 1000000000)

register_simp_attr dbgSimp

register_simp_attr compilerSimp
