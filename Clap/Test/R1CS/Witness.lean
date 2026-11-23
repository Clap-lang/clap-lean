import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg
import Clap.Model.eDSL

/-!
# Witness generation

`Circuit.toWg` fills its expression cache gate by gate, so a gate may read the outputs of earlier
-/

namespace Clap.Test.R1CS.Witness

open HashConsM
open Clap.ConstraintSystem

private instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- fpmul with 4-bit limbs on `k` limbs of a, b, p' (inputs 0…3k-1), and a share of each limb of
`r`. -/
def fpmulK (k : ℕ) : ClapM 65537 Unit := do
  let a ← Vector.ofFnM fun (i : Fin k) ↦ liftM (mkVar (p := 65537) i)
  let b ← Vector.ofFnM fun (i : Fin k) ↦ liftM (mkVar (p := 65537) (k + i))
  let m ← Vector.ofFnM fun (i : Fin k) ↦ liftM (mkVar (p := 65537) (2 * k + i))
  let r ← fpmul 4 k a b m
  for e in r.toArray do
    discard <| share e

/-- `toCs` holds on `toWg`'s trace, and the trace's `r` and its shares. -/
private def fpmulKRun (k : ℕ) (inputs : Vector (ZMod 65537) (3 * k)) : Bool × List ℕ :=
  let circuit := (fpmulK k).getCircuit (3 * k) {}
  let σ := (fpmulK k).getHashConsState (3 * k) {}
  let slots := (circuit.toWg σ (3 * k)).run? inputs |>.toOption.getD #[]
  ((circuit.toCs σ (3 * k)).run slots,
    (List.range (2 * k)).map fun v ↦ (slots[3 * k + offsetIdx circuit v]?.getD 0).val)

-- 143 = 10·14 + 3; 3000·2500 = 1832·4093 + 1624 and 1624 = (8, 5, 6) in 4-bit limbs.
example : fpmulKRun 1 #v[13, 11, 14] == (true, [3, 3]) := by native_decide
example : fpmulKRun 2 #v[8, 12, 6, 9, 11, 15] == (true, [3, 8, 3, 8]) := by native_decide
example : fpmulKRun 3 #v[8, 11, 11, 4, 12, 9, 13, 15, 15] == (true, [8, 5, 6, 8, 5, 6]) := by
  native_decide
-- 29333·5859 = 4214·40779 + 19341, and 19341 = (13, 8, 11, 4) in 4-bit limbs.
example : fpmulKRun 4 #v[5, 9, 2, 7, 3, 14, 6, 1, 11, 4, 15, 9] ==
    (true, [13, 8, 11, 4, 13, 8, 11, 4]) := by native_decide

end Clap.Test.R1CS.Witness
