import Lean

import Lean.Meta.Sym.SymM

namespace Clap.Compiler.Sets.Functional

/--
This is more or less `Lean.Meta.Tactic.Cbv.betaReduce`, which seems to not be exported.
-/
def betaReduce : Lean.Meta.Sym.Simp.Simproc := fun e ↦ do
  let (function@(.lam ..), args@⟨(.cons _ _)⟩) := e.withApp (·, ·) | return .rfl
  let e' ← Lean.Meta.Sym.betaS function args
  trace[Clap.Compile.simp.proc.beta]
    m!"\nf = {function}\nargs[{args.size}] = {args}"
  return .step e' (←Lean.Meta.Sym.mkEqRefl e')

end Clap.Compiler.Sets.Functional
