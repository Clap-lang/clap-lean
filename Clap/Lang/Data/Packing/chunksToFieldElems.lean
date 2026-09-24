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

/-- The chunks are determined by the scalars `chunksToFieldElems` packs them into, as long as
each chunk is below `2 ^ b` and a scalar's `cps * b` bits fit below `p`. -/
lemma toChunks_map_chunksToNum_injective {w cps b : ℕ} (h_fit : 2 ^ (cps * b) ≤ p)
    {v₁ v₂ : Vector (ZMod p) (w * cps)}
    (h₁ : ∀ i : Fin (w * cps), v₁[i].val < 2 ^ b) (h₂ : ∀ i : Fin (w * cps), v₂[i].val < 2 ^ b)
    (h : (toChunks cps v₁).map (chunksToNum b) = (toChunks cps v₂).map (chunksToNum b)) :
    v₁ = v₂ := by
  ext k hk
  have h_cps : 0 < cps := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hi : k / cps < w := (Nat.div_lt_iff_lt_mul h_cps).mpr hk
  have h_digits : ∀ {v : Vector (ZMod p) (w * cps)}, (∀ i : Fin (w * cps), v[i].val < 2 ^ b) →
      ∀ j : Fin cps, (toChunks cps v)[k / cps][j].val < 2 ^ b := fun hv j ↦ by
    simpa using hv ⟨k / cps * cps + j, toChunks_index_lt hi j.isLt⟩
  have h_chunk := congrArg (·[k / cps]) h
  simp only [Vector.getElem_map] at h_chunk
  have h_elem := congrArg (·[k % cps]'(Nat.mod_lt _ h_cps))
    (chunksToNum_injective h_fit (h_digits h₁) (h_digits h₂) h_chunk)
  simpa [Nat.div_add_mod'] using h_elem

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
