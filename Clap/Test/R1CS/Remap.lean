import Clap.Model.Ref.ToCs

namespace Clap.Test.R1CS.Remap

open Clap.ConstraintSystem

/-! ### Variables to trace slots

`offsetHashConsState` puts each ClapM variable at the trace slot `slotTable` gives -/

/-- The old and the new remap agree on every variable, up to 3 past the gates' outputs. -/
def remapsAgree (circuit : Circuit) : Bool :=
  (List.range (circuit.numAllocStep + 3)).all fun i ↦ offsetIdx circuit i == offsetIdxRef circuit i

/-- A circuit of `len` gates drawn from eq0, share, isZero and num2bits 0–5 (a linear
congruential generator from `seed`). The remap only reads the gates, not their arguments. -/
private def randomCircuit (seed len : ℕ) : Circuit := Id.run do
  let mut s := seed
  let mut c : Circuit := #[]
  for _ in [0:len] do
    s := (s * 1103515245 + 12345) % 2147483648
    c := c.push <| match s / 65536 % 5 with
      | 0 => .eq0 0
      | 1 => .share 0
      | 2 => .isZero 0
      | _ => .num2bits (s / 8 % 6) 0
  return c

example : remapsAgree #[] := by native_decide
example : remapsAgree #[.isZero 0] := by native_decide
example : remapsAgree #[.share 0, .isZero 1, .num2bits 3 2, .eq0 3, .isZero 4, .num2bits 0 0,
    .share 5, .isZero 6, .eq0 7, .num2bits 2 8, .isZero 9] := by native_decide
example : (List.range 24).all (fun seed ↦ remapsAgree (randomCircuit seed (3 * seed))) := by
  native_decide

/-! ### fpmul

`fpMul_impl` and `WitnessGenerator.fpMulUnsafe` lay a block out the same way, with the output `r`
in the middle: for w = 4, k = 2 it starts at slot 3·2·4 + 3 + 2·5 = 37 of the block's 82 (the last
2 are `check_lt`'s shared flags). -/

example : offsetIdx #[.fpmul 4 2 #v[0, 0] #v[0, 0] #v[0, 0], .share 0] 0 == 37 &&
    offsetIdx #[.fpmul 4 2 #v[0, 0] #v[0, 0] #v[0, 0], .share 0] 1 == 38 &&
    offsetIdx #[.fpmul 4 2 #v[0, 0] #v[0, 0] #v[0, 0], .share 0] 2 == 82 := by native_decide
-- The old remap put r at 51 and 52.
example : offsetIdxRef #[.fpmul 4 2 #v[0, 0] #v[0, 0] #v[0, 0], .share 0] 0 == 51 := by
  native_decide

end Clap.Test.R1CS.Remap
