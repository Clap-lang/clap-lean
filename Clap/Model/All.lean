import Clap.Model.AllocatedProgram
import Clap.Model.Circuit
import Clap.Model.CircuitEvalSt
import Clap.Model.ConstraintSystem.eq0
import Clap.Model.ConstraintSystem.fpMul
import Clap.Model.ConstraintSystem.isZero
import Clap.Model.ConstraintSystem.num2bits
import Clap.Model.ConstraintSystem.share
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.Convert.Base
import Clap.Model.Convert.PaddedVector
import Clap.Model.Convert.Specialised
import Clap.Model.eDSL
import Clap.Model.Expr
import Clap.Model.Gate
import Clap.Model.HashCons.CacheExpr
import Clap.Model.HashCons.Eval
import Clap.Model.HashCons.HashConsM
import Clap.Model.HashCons.HashConsSt
import Clap.Model.Monad
import Clap.Model.PublicInput
import Clap.Model.Varstore
import Clap.Model.WitnessGenerator.eq0
import Clap.Model.WitnessGenerator.fpMul
import Clap.Model.WitnessGenerator.isZero
import Clap.Model.WitnessGenerator.num2bits
import Clap.Model.WitnessGenerator.share
import Clap.Model.WitnessGenerator.toWg

/-!
# The CLAP model

Everything the `ClapM p` model is made of: the hash-consed expression heap, the circuit monad
and its semantics, the refinement layer (`Conversion` / `Converts` / `ConvertsM`), and the two
back ends — lowering to a constraint system and witness generation.

Nothing here may import `Clap.Lang.*`: the gadget library is built *on* this module, not the
other way round. See [docs/repo-layout.md](../../docs/repo-layout.md).
-/
