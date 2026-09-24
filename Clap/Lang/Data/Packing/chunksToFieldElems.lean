import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.FB.assert
import Clap.Lang.Data.FVec.eq
import Clap.Lang.Data.Packing.chunksToFieldElem

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- Pack `w * chunksPerScalar` chunks into `w` field elements, `chunksPerScalar` per element,
each little-endian as in `chunksToFieldElem`.

The chunk count is an exact multiple. Circom also allows a shorter last
scalar, callers pad with zero chunks instead, which gives the same values because the chunks are
little-endian  -/
def chunksToFieldElems {w : ℕ} (chunksPerScalar bitsPerChunk : ℕ)
    (chunks : FVec p (w * chunksPerScalar)) : ClapM p (FVec p w) :=
  (toChunks chunksPerScalar chunks).mapM (chunksToFieldElem bitsPerChunk)

namespace chunksToFieldElems

lemma convertsM
  {w chunksPerScalar bitsPerChunk : ℕ}
  {state : ClapMState p}
  {chunks : FVec p (w * chunksPerScalar)}
  {vals : Vector (ZMod p) (w * chunksPerScalar)}
  (h_chunks : Converts FVec.conversion state chunks vals)
:
  ConvertsM FVec.conversion (chunksToFieldElems chunksPerScalar bitsPerChunk chunks) state
    ((toChunks chunksPerScalar vals).map (chunksToNum bitsPerChunk)) True
:= convertsM_mapM (FVec.converts_toChunks h_chunks) chunksToFieldElem.convertsM

end chunksToFieldElems

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeChunksToFieldElemsQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check {w : ℕ} (cps b : ℕ) (chunks : Vector (ZMod q) (w * cps))
    (expected : Vector (ZMod q) w) : ClapM q Unit := do
  let cs ← chunks.mapM mkF
  let rs ← chunksToFieldElems cps b cs
  let es ← expected.mapM mkF
  assert (← FVec.eq rs es)

private def sat {w : ℕ} (cps b : ℕ) (chunks : Vector (ZMod q) (w * cps))
    (expected : Vector (ZMod q) w) : Bool :=
  let c := check cps b chunks expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

-- `[00₂, 11₂, 10₂, 01₂, 11₂, 10₂] ↦ 101100₂, 101101₂`
example : sat (w := 2) 3 2 #v[0, 3, 2, 1, 3, 2] #v[44, 45] = true := by native_decide
example : sat (w := 6) 1 2 #v[0, 3, 2, 1, 3, 2] #v[0, 3, 2, 1, 3, 2] = true := by native_decide
example : sat (w := 2) 3 1 #v[0, 1, 1, 1, 0, 0] #v[6, 1] = true := by native_decide
example : sat (w := 2) 3 2 #v[0, 3, 2, 1, 3, 2] #v[45, 44] = false := by native_decide

end examples

end Clap.Lang.Packing
