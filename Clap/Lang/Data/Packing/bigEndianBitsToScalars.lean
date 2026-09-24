import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.FB.assert
import Clap.Lang.Data.FVec.eq
import Clap.Lang.Data.Packing.bigEndianBits2Num

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- Cut a bit vector into `w` chunks of `bitsPerScalar` bits and read each chunk big-endian.

The bit count is an exact multiple. Circom also allows a shorter last
scalar, but unlike `chunksToFieldElems` a big-endian chunk cannot be zero-padded without changing
its value and Keyless never needs it. -/
def bigEndianBitsToScalars {w : ℕ} (bitsPerScalar : ℕ) (bits : FArray p (w * bitsPerScalar)) : ClapM p (FVec p w) :=
  (toChunks bitsPerScalar bits).mapM bigEndianBits2Num

namespace bigEndianBitsToScalars

lemma convertsM
  [p.AtLeastTwo]
  {w bitsPerScalar : ℕ}
  {state : ClapMState p}
  {bits : FArray p (w * bitsPerScalar)}
  {bits_val : Vector Bool (w * bitsPerScalar)}
  (h_bits : Converts FArray.conversion state bits bits_val)
:
  ConvertsM FVec.conversion (bigEndianBitsToScalars bitsPerScalar bits) state
    ((toChunks bitsPerScalar bits_val).map fun c ↦ FArray.toNum c.reverse) True
:= convertsM_mapM (FArray.converts_toChunks h_bits) bigEndianBits2Num.convertsM

end bigEndianBitsToScalars

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeBigEndianBitsToScalarsQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check {w : ℕ} (bps : ℕ) (bits : Vector Bool (w * bps))
    (expected : Vector (ZMod q) w) : ClapM q Unit := do
  let bs ← bits.mapM FB.ofBool
  let rs ← bigEndianBitsToScalars bps bs
  let es ← expected.mapM mkF
  assert (← FVec.eq rs es)

private def sat {w : ℕ} (bps : ℕ) (bits : Vector Bool (w * bps))
    (expected : Vector (ZMod q) w) : Bool :=
  let c := check bps bits expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat (w := 3) 4
    #v[false, false, false, false, false, false, false, true, false, false, true, true]
    #v[0, 1, 3] = true := by native_decide
example : sat (w := 3) 4
    #v[false, false, false, false, false, false, false, true, false, true, true, false]
    #v[0, 1, 6] = true := by native_decide
example : sat (w := 3) 4
    #v[false, false, false, false, false, false, false, true, false, true, true, false]
    #v[0, 1, 3] = false := by native_decide

end examples

end Clap.Lang.Packing
