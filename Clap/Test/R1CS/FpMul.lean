import Clap.Model.ConstraintSystem.fpMul
import Clap.Model.WitnessGenerator.fpMul

/-!
# fpmul: the constraint and witness sides agree

`check_lt` shares each limb's running flag (Clap/Model/ConstraintSystem/fpMul.lean), so both sides
gain one slot per limb.
-/

namespace Clap.Test.R1CS.FpMul

open Clap.ConstraintSystem

-- The constraint side's slot count is the witness generator's trace size.
example : (List.range 10).all fun w ↦ (List.range 8).all fun k ↦
    fpMul.numAllocStep w k == WitnessGenerator.fpMul.trace_capacity k w := by native_decide

end Clap.Test.R1CS.FpMul
