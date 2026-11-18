import Clap.Model.eDSL

/-!
# Gate outputs are `BoundRef p`

`share`, `isZero`, `num2bits` and `fpmul` return `BoundRef p`, so `p` comes from the outputs. With
a forgotten `←`, `u * u` on two outputs is a type error instead of ℕ multiplication of heap
indices.
-/

namespace Clap.Test.GateOutputs

open HashConsM

/--
error: Type mismatch
  u * u
has type
  ClapM 7 (BoundRef 7)
but is expected to have type
  ExprRef
-/
#guard_msgs in
example : ClapM 7 Unit := do
  let x ← liftM (mkVar (p := 7) 0)
  let u ← share x
  let v ← share (u * u)
  eq0 v

end Clap.Test.GateOutputs
