import Lean

namespace Clap

structure StepState where
  lastLemmaUserName : Lean.Name -- Maybe just `FVarId`, but this is easier for me to read
  deriving Inhabited

/--
TODO: We can do `async` on the extension if we expand the storage to 'last lemma' per proof.
      This currently blocks.
-/
initialize stepExt : Lean.EnvExtension StepState ←
  Lean.registerEnvExtension (pure default) (asyncMode := .sync)

end Clap
