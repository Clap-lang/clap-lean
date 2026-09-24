import Clap.Lang.Data.FArray.bits2num
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Core.FUnit.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- The field element a bit vector denotes, most significant bit first. -/
def bigEndianBits2Num {w : ℕ} (bits : FArray p w) : ClapM p (F p) :=
  FArray.bits2num bits.reverse

namespace bigEndianBits2Num

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {bits : FArray p w}
  {bits_val : Vector Bool w}
  (h_bits : Converts FArray.conversion state bits bits_val)
:
  ConvertsM F.conversion (bigEndianBits2Num bits) state (FArray.toNum bits_val.reverse) True
:= FArray.bits2num.convertsM (FArray.converts_reverse h_bits)

end bigEndianBits2Num

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeBigEndianBits2NumQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check {w : ℕ} (bits : Vector Bool w) (expected : ZMod q) : ClapM q Unit := do
  let b ← bits.mapM FB.ofBool
  let r ← bigEndianBits2Num b
  assert_eq r (← mkF expected)

private def sat {w : ℕ} (bits : Vector Bool w) (expected : ZMod q) : Bool :=
  let c := check bits expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat #v[] 0 = true := by native_decide
example : sat #v[false] 0 = true := by native_decide
example : sat #v[true, true, false, false] 12 = true := by native_decide
-- the least-significant-first reading of the same bits
example : sat #v[true, true, false, false] 3 = false := by native_decide

end examples

end Clap.Lang.Packing
