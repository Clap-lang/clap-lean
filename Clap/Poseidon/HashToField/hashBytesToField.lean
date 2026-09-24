import Clap.Poseidon.HashToField.hashElemsToField
import Clap.Lang.Data.Packing.assertIsBytes
import Clap.Lang.Data.Packing.chunksToFieldElems
import Clap.Model.Convert.PaddedVector

namespace Clap.HashToField

open Lang Poseidon Primes

-- See `hashElemsToField.lean`.
attribute [local irreducible] Clap.poseidonBN254

/-- Hash `numBytes` bytes and a length to one field element. Range-checks the bytes,
packs them 31 per field element (zero-padding the last), appends `input.len`, and hashes the
result with `hashElemsToField`.

All `numBytes` bytes are hashed, not only the first `len`. Circom's comment that bytes past
`len` "are ignored" is wrong: `ChunksToFieldElems` packs the whole array. So the ideal value is a
function of the full padded data and `len`, and binding a string needs its padding to be zero,
which `FString.conversion` supplies.

Collision resistance holds only at a fixed `numBytes`, because `hashElemsToField` is not
domain-separated by size: with `len` unconstrained, a 31-byte instance can reproduce the hash of a
466–961-byte one. Callers that range-check `len` are unaffected.

Slot 5 is the byte range check `∀ i, data_vals[i].val < 2 ^ 8` from `Packing.assertIsBytes`,
on which the model and the compiled circuit agree. -/
def hashBytesToField {numBytes : ℕ} (input : FString bn254 numBytes) : ClapM bn254 (F bn254) := do
  Packing.assertIsBytes input.data
  let pad ← mkF 0
  let padded : FVec bn254 ((numBytes + 30) / 31 * 31) := (input.data ++ Vector.replicate ((numBytes + 30) / 31 * 31 - numBytes) pad).cast (by omega)
  let elems ← Packing.chunksToFieldElems 31 8 padded
  hashElemsToField (elems.push input.len)

/-- The ideal value of `hashBytesToField` -/
def hashBytesToFieldSpec (H : HashFn) {numBytes : ℕ} (data : Vector (ZMod bn254) numBytes)
    (len : ZMod bn254) : ZMod bn254 :=
  let padded : Vector (ZMod bn254) ((numBytes + 30) / 31 * 31) :=
    (data ++ Vector.replicate ((numBytes + 30) / 31 * 31 - numBytes) (0 : ZMod bn254)).cast (by omega)
  hashElemsToFieldSpec H (((toChunks 31 padded).map (Packing.chunksToNum 8)).push len)

namespace hashBytesToField

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {numBytes : ℕ}
  {state : ClapMState bn254}
  {input : FString bn254 numBytes}
  {data_vals : Vector (ZMod bn254) numBytes}
  {len_val : ZMod bn254}
  (h_data : Converts FVec.conversion state input.data data_vals)
  (h_len : Converts F.conversion state input.len len_val)
  (h_numBytes : numBytes ≤ 1953)
:
  ConvertsM F.conversion (hashBytesToField input) state (hashBytesToFieldSpec H data_vals len_val) (∀ i : Fin numBytes, data_vals[i].val < 2 ^ 8)
:= by
  unfold hashBytesToField hashBytesToFieldSpec
  step Packing.assertIsBytes.convertsM h_data as check
  step mkF.convertsM as pad
  dsimp only  -- the definition's `let padded`, which `step` cannot see through
  have h_padded := FVec.converts_vector_cast
    (FVec.converts_append h_data
      (FVec.converts_replicate (k := (numBytes + 30) / 31 * 31 - numBytes) h_pad))
    (show numBytes + ((numBytes + 30) / 31 * 31 - numBytes) = (numBytes + 30) / 31 * 31 by omega)
  step Packing.chunksToFieldElems.convertsM h_padded as elems
  have h_elems_len := FVec.converts_push h_elems h_len
  apply convertsM_of_convertsM
    (hashElemsToField.convertsM h_H h_elems_len (by omega) (by omega))
  . rfl
  . simp
  . exact id  -- `step`'s leftover from `assertIsBytes`: the byte check implies itself

end hashBytesToField

section examples

/-- `hashBytesToField` of `msg` zero-padded to `numBytes`, with `len = msg.length`. -/
private def bytesHash (numBytes : ℕ) (msg : List ℕ) : Option (ZMod bn254) :=
  let cmd : ClapM bn254 (HashConsSt bn254 × ExprRef) := do
    let data ← (Vector.ofFn (n := numBytes) fun i ↦ ((msg.getD i.val 0 : ℕ) : ZMod bn254)).mapM
      (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let len ← liftM (HashConsM.mkConstant (p := bn254) (msg.length : ZMod bn254))
    let z ← hashBytesToField ⟨data, len⟩
    let σ ← getThe (HashConsSt bn254)
    return (σ, z)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

-- one element: `[pack msg, 6]`
example : bytesHash 6 [147, 139, 223, 159, 166, 20] =
  some 13994610850800277351346694935735956205500166458544915277495466551921036587172 := by
  native_decide

-- two elements, the second all padding: `[pack msg, 0, 5]`
example : bytesHash 62 [1, 2, 3, 4, 5] =
  some 17891043070668315820315565801110254287516103649870519663767767541403051744030 := by
  native_decide

-- one full element and one partial: `[pack 1..31, pack 32..40, 40]`
example : bytesHash 62 ((List.range 40).map (· + 1)) =
  some 19364146746416071195829466169360764847138059406444764150757486565697969237878 := by
  native_decide

-- `Poseidon [0, 1, 62]`
example : bytesHash 62 (List.replicate 31 0 ++ [1] ++ List.replicate 30 0) =
  some 15108995961371611790528033672782068063008181353996387970156202240921543829585 := by
  native_decide

-- `Poseidon [0, 0, 62]`
example : bytesHash 62 (List.replicate 62 0) =
  some 18955193024213499903276022608734737644948951344086434322069232702331459314690 := by
  native_decide

/-- `hashElemsToField` of constant inputs. -/
private def elemsHash {n : ℕ} (xs : Vector (ZMod bn254) n) : Option (ZMod bn254) :=
  let cmd : ClapM bn254 (HashConsSt bn254 × ExprRef) := do
    let refs ← xs.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let z ← hashElemsToField refs
    let σ ← getThe (HashConsSt bn254)
    return (σ, z)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

-- `Poseidon [0, 0, 0]`
example : elemsHash #v[0, 0, 0] =
  some 5317387130258456662214331362918410991734007599705406860481038345552731150762 := by
  native_decide

end examples

end Clap.HashToField
