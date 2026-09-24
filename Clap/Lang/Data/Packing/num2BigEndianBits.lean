import Clap.Lang.Gate.num2bits
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Data.FArray.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- The `w`-bit decomposition of `e`, most significant bit first.

Slot 5 is `num2bits`' range check `e_val.val < 2 ^ w`: Circom's "acts as a range check for the
input number being in `[0, 2^N)`" holds of the model as of the compiled circuit, which the
tests below show rejecting `16` at `w = 4`. -/
def num2BigEndianBits (w : ℕ) (e : F p) : ClapM p (FArray p w) := do
  let bits ← num2bits w e
  return bits.reverse

namespace num2BigEndianBits

lemma convertsM
  {w : ℕ}
  {state : ClapMState p}
  {e : F p}
  {e_val : ZMod p}
  (h_e : Converts F.conversion state e e_val)
:
  ConvertsM FArray.conversion (num2BigEndianBits w e) state ((num2bitsLsbPureV w e_val).map (· == 1)).reverse (e_val.val < 2 ^ w)
:= by
  unfold num2BigEndianBits
  step num2bits.convertsM h_e as bits
  apply convertsM_pure
  · exact FArray.converts_reverse h_bits
  · exact id

end num2BigEndianBits

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeNum2BigEndianBitsQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check (w : ℕ) (x : ZMod q) (expected : Vector Bool w) : ClapM q Unit := do
  let e ← mkF x
  let bits ← num2BigEndianBits w e
  let exp ← expected.mapM FB.ofBool
  FArray.assert_eq bits exp

private def sat (w : ℕ) (x : ZMod q) (expected : Vector Bool w) : Bool :=
  let c := check w x expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat 4 5 #v[false, true, false, true] = true := by native_decide
-- the least-significant-first order is wrong
example : sat 4 5 #v[true, false, true, false] = false := by native_decide
example : sat 8 255 (Vector.replicate 8 true) = true := by native_decide
-- out of range: slot 5 fails (`16 ≥ 2^4`), and the circuit rejects
example : sat 4 16 (Vector.replicate 4 false) = false := by native_decide

end examples

end Clap.Lang.Packing
