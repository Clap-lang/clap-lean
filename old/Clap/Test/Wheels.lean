import Lean

open Lean

namespace Clap

namespace Test

/--
Used to find constants that are guaranteed to exist.
Considering we use this during testing, we just panic on goof.
-/
def find! (ident : Name) : MetaM ConstantInfo := do
  return ((←getEnv).find? (←realizeGlobalConst (mkIdent ident))[0]!).get!

end Test

end Clap
