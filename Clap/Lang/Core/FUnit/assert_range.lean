import Clap.Lang.Gate.num2bits
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang

variable {p : ℕ}

def assert_range (w : ℕ) (e : F p) : ClapM p Unit := do
  let _ ← num2bits w e
  return ()

namespace assert_range

lemma convertsM
  {state}
  {w : ℕ}
  {e : F p}
  {e_val : ZMod p}
  (h_e : Converts F.conversion state e e_val)
:
  ConvertsM FUnit.conversion (assert_range w e) state () (e_val.val < 2 ^ w)
:= by
  unfold assert_range
  step num2bits.convertsM h_e as bits
  apply convertsM_pure
  · exact FUnit.converts
  · exact id

section examples

private abbrev q : ℕ := 47

local instance instFactPrimeAssertRangeQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- `assert_range 4` applied to a single public input. -/
private def rangeCheck : ClapM q Unit := do
  let x ← liftM (HashConsM.mkVar (p := q) 0)
  assert_range 4 x

private def sat (x : ZMod q) : Bool :=
  let circ  := rangeCheck.getCircuit 1 (HashConsSt.empty q)
  let cache := rangeCheck.getHashConsState 1 (HashConsSt.empty q)
  (circ.toCs cache 1).run ((circ.toWg cache 1).run #v[x])

example : sat 0  = true  := by native_decide
example : sat 5  = true  := by native_decide
example : sat 15 = true  := by native_decide
-- out of range: slot 5 fails, and the circuit is unsatisfiable
example : sat 16 = false := by native_decide
example : sat 20 = false := by native_decide
example : sat 31 = false := by native_decide

end examples

end assert_range

end Clap.Lang
