import Clap.Lang
import Clap.Packing
import Clap.Poseidon.Poseidon

namespace HashToField

open Clap.Lang

abbrev p := Clap.Poseidon.p

/-
  There is a `{maxbits}` tag in keyless which seems to be set to 64.
-/
def hash64BitLimbsToField {numLimbs : ℕ}
  (input : PaddedVector F p numLimbs) :
  Option (F p)
:=
  let len := input.len
  let input := input.data
  assert! numLimbs != 0
  let w := (numLimbs + 2) / 3
  let padded : Vector (F p) (w * 3) :=
    have h : numLimbs ≤ w * 3 := by omega
    Nat.add_sub_cancel' h ▸ (input ++ Vector.replicate (w * 3 - numLimbs) (0 : F p))
  let elems := Packing.chunksToFieldElems (p := p) 3 64 padded
  let elems := elems.push len
  Clap.Poseidon.poseidonBN254 elems

-- TODO keyless requires n ≤ 64, why?
def hashElemsToField {n : ℕ} (input : Vector (F p) n) : Option (F p) := do
  if n ≤ 16 then
    Clap.Poseidon.poseidonBN254 input
  else if n ≤ 32 then
    let h1 ← Clap.Poseidon.poseidonBN254 (input.extract  0 16)
    let h2 ← Clap.Poseidon.poseidonBN254 (input.extract 16 32)
    Clap.Poseidon.poseidonBN254 #v[h1,h2]
  else if n ≤ 48 then
    let h1 ← Clap.Poseidon.poseidonBN254 (input.extract  0 16)
    let h2 ← Clap.Poseidon.poseidonBN254 (input.extract 16 32)
    let h3 ← Clap.Poseidon.poseidonBN254 (input.extract 32 48)
    Clap.Poseidon.poseidonBN254 #v[h1,h2,h3]
  else if n ≤ 64 then
    let h1 ← Clap.Poseidon.poseidonBN254 (input.extract  0 16)
    let h2 ← Clap.Poseidon.poseidonBN254 (input.extract 16 32)
    let h3 ← Clap.Poseidon.poseidonBN254 (input.extract 32 48)
    let h4 ← Clap.Poseidon.poseidonBN254 (input.extract 48 64)
    Clap.Poseidon.poseidonBN254 #v[h1,h2,h3,h4]
  else (0:F p)

/-
TODO it's unclear if the Packing.assertIsBytes is always needed, we could move it to a precondition
TODO Comment in keyless says "Only input.len bytes are actually hashed". How/why?
TODO In keyless ChinksToFieldElems can return numBytes or numBytes+1
-/
def hashBytesToField {numBytes : ℕ}
  (input : PaddedVector F p numBytes) :
  Option (F p)
:= do
  let len := input.len
  let input := input.data
  assert! numBytes != 0
  Packing.assertIsBytes input
  let w := (numBytes + 30) / 31
  let padded : Vector (F p) (w * 31) :=
    have h : numBytes ≤ w * 31 := by omega
    Nat.add_sub_cancel' h ▸ (input ++ Vector.replicate (w * 31 - numBytes) (0 : F p))
  let elems := Packing.chunksToFieldElems (p := p) 31 8 padded
  let elems := elems.push len
  hashElemsToField elems

end HashToField

namespace TestHashToField

open HashToField
open Clap.Lang

abbrev p := Primes.bn254

-- from circuit/src/hash_to_field.rs `print_hashtofield_vectors`
-- run with `cargo test -p aptos-keyless-circuit print_hashtofield_vectors -- --nocapture`
-- (preserved generator: Clap/HashToField_rust/)

private def bytes5PadTo62 : Vector (F p) 62 := Vector.append #v[1, 2, 3, 4, 5] (Vector.replicate 57 (0 : F p))
private def bytes1to40PadTo62 : Vector (F p) 62 :=
  Vector.append
    #v[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
    (Vector.replicate 22 (0 : F p))

-- msg=[147,139,223,159,166,20] cap = 6 len = 6 -> elems = [pack(msg), 6]
example : hashBytesToField ⟨#v[147,139,223,159,166,20], 6⟩ ==
  some 13994610850800277351346694935735956205500166458544915277495466551921036587172
:= by native_decide

-- msg=[1,2,3,4,5] cap = 62 len = 5 -> 2 scalars (2nd from padding = 0), elems = [pack(msg,0..), 0, 5]
example : hashBytesToField ⟨bytes5PadTo62, 5⟩ ==
  some 17891043070668315820315565801110254287516103649870519663767767541403051744030
:= by native_decide

-- msg=bytes 1..40 cap = 62 len = 40 -> elems = [pack(1..31), pack(32..40,0..), 40]
example : hashBytesToField ⟨bytes1to40PadTo62, 40⟩ ==
  some 19364146746416071195829466169360764847138059406444764150757486565697969237878
:= by native_decide

private def chunk31BytesZero : Vector (F p) 31 :=
  Vector.replicate 31 0
private def chunk31BytesOne : Vector (F p) 31 :=
  Vector.append #v[1] (Vector.replicate 30 0)

example : hashBytesToField ⟨chunk31BytesZero ++ chunk31BytesOne, 31 + 31⟩ ==
  /- poseidon [0, 1, 62] -/
  some 15108995961371611790528033672782068063008181353996387970156202240921543829585
:= by
  native_decide

example : hashBytesToField ⟨chunk31BytesZero ++ chunk31BytesZero, 31 + 31⟩ ==
  /- poseidon [0, 0, 62] -/
  some 18955193024213499903276022608734737644948951344086434322069232702331459314690
:= by
  native_decide

example :
  hashElemsToField #v[0, 0, 0] ==
    /- poseidon [0,0,0] -/
    some 5317387130258456662214331362918410991734007599705406860481038345552731150762
:= by
  native_decide

example :
  hashElemsToField (Vector.replicate (3*16 + 3) 1) ==
    /-
      poseidon
        [poseidon [1..1], poseidon [1..1], poseidon [1..1], poseidon [1,1,1]]
    -/
    .some 11628121580149142260524838530806013087501953643589744849802502906921824536992
:= by
  native_decide

-- from circuit/src/hash_to_field.rs `print_hashtofield_vectors`
-- keyless appends len = numLimbs (the number of limbs), not numLimbs*8
-- limbs = [1,0,0, 2,0,0] cap = 6 len = 6 -> elems = [1, 2, 6]
example : hash64BitLimbsToField ⟨#v[1,0,0, 2,0,0], 6⟩ ==
  some 12357238260310637995943135375585171688556280490812423735142467946729167059695
:= by native_decide

-- limbs = [0,1,0] cap = 3 len = 3 -> elems = [2^64, 3]
example : hash64BitLimbsToField ⟨#v[0,1,0], 3⟩ ==
  some 14123858125510765373592556917469506021879873191038230502015132317060124997248
:= by native_decide

-- limbs = [1,2] cap = 6 len = 2 -> 2 scalars (2nd from padding = 0), elems = [1+2*2^64, 0, 2]
example : hash64BitLimbsToField ⟨#v[1,2,0,0,0,0], 2⟩ ==
  some 8309192594278154676795975429535953516065089753051187486831405226925285963049
:= by native_decide

end TestHashToField
