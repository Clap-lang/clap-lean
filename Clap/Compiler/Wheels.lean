import Lean
-- import Lean.Util.PtrSet
-- import Lean.Declaration

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

initialize Lean.registerTraceClass `Clap.Compile.simp.fail (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.config (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.kaboom (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.warnDownNotGround (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.getElem_mk (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.mk_append_mk (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.vector_mapM_mk_eq_append (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.sequenceAsVecExpr (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.zeta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.evalGround (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.vector_getElem_mk (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.simp.proc.seemsTotallySafeInDTT (inherited := true)

initialize Lean.registerTraceClass `Clap.Compile.debug.simp (inherited := true)


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

register_simp_attr dbgSimp

register_simp_attr compilerSimp

-- /-
-- Based on `Expr.getUsedConstants`.
-- -/

-- namespace Lean
-- namespace Expr
-- namespace FoldConstsImpl

-- unsafe structure State' where
--  visited       : PtrSet Expr := mkPtrSet
--  visitedConsts : NameHashSet := {}

-- unsafe def fold' {α : Type} (f : Name → α → α) (e : Expr) (acc : α) : StateT State MetaM α :=
--   let rec visit (e : Expr) (acc : α) : StateT State MetaM α := do
--     if (←Meta.inferType e).isProp then
--       logInfo m!"Rejected: {e} with T: {←Meta.inferType e}"
--       return acc
--     if (← get).visited.contains e then
--       return acc
--     modify fun s => { s with visited := s.visited.insert e }
--     match e with
--     | .forallE _ d b _   => visit b (← visit d acc)
--     | .lam _ d b _       => visit b (← visit d acc)
--     | .mdata _ b         => visit b acc
--     | .letE _ t v b _    => visit b (← visit v (← visit t acc))
--     | .app f a           => visit a (← visit f acc)
--     | .proj _ _ b        => visit b acc
--     | .const c _         =>
--       if (← get).visitedConsts.contains c then
--         return acc
--       else
--         modify fun s => { s with visitedConsts := s.visitedConsts.insert c };
--         return f c acc
--     | _ => return acc
--   visit e acc

-- @[inline] unsafe def foldUnsafe' {α : Type} (e : Expr) (init : α) (f : Name → α → α) : MetaM α :=
--   (fold' f e init).run' {}

-- end FoldConstsImpl

-- /-- Apply `f` to every constant occurring in `e` once. -/
-- @[implemented_by FoldConstsImpl.foldUnsafe']
-- opaque foldConsts' {α : Type} (e : Expr) (init : α) (f : Name → α → α) : MetaM α := return init

-- def getUsedConstants' (e : Expr) : MetaM (Array Name) :=
--   e.foldConsts' #[] fun c cs => cs.push c

-- end Expr
-- end Lean
