import Clap.Poseidon.Computes
import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.Packing.chunksToFieldElems
import Clap.Model.Convert.PaddedVector

namespace Clap.HashToField

open Lang Poseidon Primes

-- See `hashElemsToField.lean`.
attribute [local irreducible] Clap.poseidonBN254

/-- Hash `numLimbs` 64-bit limbs and a length to one field element. Packs the limbs 3 per field
element (zero-padding the last), appends `input.len`, and hashes with a single `Poseidon`.

Nothing is range-checked: Circom relies on the `{maxbits}` tag of its input, and Keyless calls
`AssertIs64BitLimbs` on the modulus separately. `len` is hashed as
given. Keyless passes the byte count `256` for the RSA modulus, while the Rust test vectors below
(`pad_and_hash_limbs_with_len`) use the limb count. -/
def hash64BitLimbsToField {numLimbs : ℕ} (input : PaddedVector (F bn254) bn254 numLimbs) :
    ClapM bn254 (F bn254) := do
  let pad ← mkF 0
  let padded : FVec bn254 ((numLimbs + 2) / 3 * 3) := (input.data ++ Vector.replicate ((numLimbs + 2) / 3 * 3 - numLimbs) pad).cast (by omega)
  let elems ← Packing.chunksToFieldElems 3 64 padded
  poseidonBN254 (elems.push input.len)

/-- The ideal value of `hash64BitLimbsToField` -/
def hash64BitLimbsToFieldSpec (H : HashFn) {numLimbs : ℕ} (limbs : Vector (ZMod bn254) numLimbs)
    (len : ZMod bn254) : ZMod bn254 :=
  let padded : Vector (ZMod bn254) ((numLimbs + 2) / 3 * 3) :=
    (limbs ++ Vector.replicate ((numLimbs + 2) / 3 * 3 - numLimbs) (0 : ZMod bn254)).cast
      (by omega)
  H (((toChunks 3 padded).map (Packing.chunksToNum 64)).push len)

namespace hash64BitLimbsToField

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {numLimbs : ℕ}
  {state : ClapMState bn254}
  {input : PaddedVector (F bn254) bn254 numLimbs}
  {limbs_vals : Vector (ZMod bn254) numLimbs}
  {len_val : ZMod bn254}
  (h_limbs : Converts FVec.conversion state input.data limbs_vals)
  (h_len : Converts F.conversion state input.len len_val)
  (h_numLimbs : numLimbs ≤ 45)
:
  ConvertsM F.conversion (hash64BitLimbsToField input) state (hash64BitLimbsToFieldSpec H limbs_vals len_val) True
:= by
  unfold hash64BitLimbsToField hash64BitLimbsToFieldSpec
  step mkF.convertsM as pad
  dsimp only  -- the definition's `let padded`, which `step` cannot see through
  have h_padded := FVec.converts_vector_cast
    (FVec.converts_append h_limbs
      (FVec.converts_replicate (k := (numLimbs + 2) / 3 * 3 - numLimbs) h_pad))
    (show numLimbs + ((numLimbs + 2) / 3 * 3 - numLimbs) = (numLimbs + 2) / 3 * 3 by omega)
  step Packing.chunksToFieldElems.convertsM h_padded as elems
  have h_elems_len := FVec.converts_push h_elems h_len
  apply convertsM_of_convertsM (h_H (by omega) (by omega) h_elems_len)
  . rfl
  . simp

end hash64BitLimbsToField

section examples

/-- `hash64BitLimbsToField` of `limbs` zero-padded to `numLimbs`, with `len = limbs.length`. -/
private def limbsHash (numLimbs : ℕ) (limbs : List ℕ) : Option (ZMod bn254) :=
  let cmd : ClapM bn254 (HashConsSt bn254 × ExprRef) := do
    let data ← (Vector.ofFn (n := numLimbs) fun i ↦ ((limbs.getD i.val 0 : ℕ) : ZMod bn254)).mapM
      (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let len ← liftM (HashConsM.mkConstant (p := bn254) (limbs.length : ZMod bn254))
    let z ← hash64BitLimbsToField ⟨data, len⟩
    let σ ← getThe (HashConsSt bn254)
    return (σ, z)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

-- two elements: `[1, 2, 6]`
example : limbsHash 6 [1, 0, 0, 2, 0, 0] =
  some 12357238260310637995943135375585171688556280490812423735142467946729167059695 := by
  native_decide

-- one element: `[2^64, 3]`
example : limbsHash 3 [0, 1, 0] =
  some 14123858125510765373592556917469506021879873191038230502015132317060124997248 := by
  native_decide

-- two elements, the second all padding: `[1 + 2 * 2^64, 0, 2]`
example : limbsHash 6 [1, 2] =
  some 8309192594278154676795975429535953516065089753051187486831405226925285963049 := by
  native_decide

end examples

end Clap.HashToField
