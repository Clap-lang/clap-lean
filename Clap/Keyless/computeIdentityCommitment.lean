import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.bracketsMap
import Clap.Lang.Data.JWT.bracketsDepthMap
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray Primes

def computeIdentityCommitment (performAudChecks : FB bn254)
  (pepper : F bn254)
  (privateAudValue : FString bn254 MAX_AUD_VALUE_LEN)
  (uidValue : FString bn254 MAX_UID_VALUE_LEN)
  (uidName  : FString bn254 MAX_UID_NAME_LEN) :
  ClapM bn254 (F bn254)
:= do
  -- Conditionally zero privateAudValue: hashable[i] = privateAudValue[i] * performAudChecks
  let hashableAud : Vector (F bn254) MAX_AUD_VALUE_LEN ←
    privateAudValue.data.mapM (mkMul performAudChecks)
  let privateAudValHashed ←
      /-
        Old clap circuit:
        `hashBytesToField {data := hashableAud,  len := privateAudValue.len * performAudChecks}`
        Original circom:
        `HashBytesToFieldWithLen(MAX_AUD_VALUE_LEN)(hashable_private_aud_value, private_aud_value_len)`
        We use len = `privateAudValue.len`, in accordance to the original circom code.
      -/
    HashToField.hashBytesToField {data := hashableAud,  len := privateAudValue.len}
  let uidValueHashed ← HashToField.hashBytesToField uidValue
  let uidNameHashed ← HashToField.hashBytesToField uidName
  Poseidon.poseidonBN254 #v[pepper, privateAudValHashed, uidValueHashed, uidNameHashed]

namespace computeIdentityCommitment

open Poseidon RandomOracle Primes HashToField

attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  {performAudChecks : FB bn254}
  {pepper : F bn254}
  {audValue : FString bn254 MAX_AUD_VALUE_LEN}
  {uidValue : FString bn254 MAX_UID_VALUE_LEN}
  {uidName : FString bn254 MAX_UID_NAME_LEN}
  {pepper_val : ZMod bn254}
  {performAudChecks_val : Bool}
  {audValue_val uidValue_val uidName_val : String}
  (h_pepper : Converts F.conversion state pepper pepper_val)
  (h_perform : Converts FB.conversion state performAudChecks performAudChecks_val)
  (h_audValue : Converts FString.conversion state audValue audValue_val)
  (h_uidValue : Converts FString.conversion state uidValue uidValue_val)
  (h_uidName : Converts FString.conversion state uidName uidName_val) :
  let uidValue_vals := encodeV (p := bn254) MAX_UID_VALUE_LEN uidValue_val
  let uidName_vals := encodeV (p := bn254) MAX_UID_NAME_LEN uidName_val
  let privateAudVal :=
    if performAudChecks_val then
      encodeV (p := bn254) MAX_AUD_VALUE_LEN audValue_val
    else
      Vector.replicate MAX_AUD_VALUE_LEN 0
  ConvertsM F.conversion
    (computeIdentityCommitment performAudChecks pepper audValue uidValue uidName)
    state
    ( H
        #v[ pepper_val,
            hashBytesToFieldSpec H privateAudVal (audValue_val.length : ZMod bn254),
            hashBytesToFieldSpec H uidValue_vals (uidValue_val.length : ZMod bn254),
            hashBytesToFieldSpec H uidName_vals (uidName_val.length : ZMod bn254)
          ]
    )
    True
  := by
  intro uidValue_vals uidName_vals privateAudVal
  unfold computeIdentityCommitment

  -- `hashableAud`: a `mapM` whose step reads the fixed `performAudChecks` as context.
  have h_perform_f := F.converts_of_FB_converts h_perform
  have h_audData := FString.converts_data h_audValue
  have h_hashableAud_raw := convertsM_mapM_ctx h_perform_f
    (fun i ↦ FVec.converts_getElem h_audData i.isLt)
    (fun h_ctx h_x ↦ mkMul.convertsM h_ctx h_x)
  have h_val_eq :
      (encodeV (p := bn254) MAX_AUD_VALUE_LEN audValue_val).map
        (fun x ↦ (if performAudChecks_val then (1 : ZMod bn254) else 0) * x) = privateAudVal := by
    simp only [privateAudVal]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    cases performAudChecks_val with
    | true => simp
    | false => simp [Vector.getElem_replicate]
  have h_hashableAud_term := convertsM_of_convertsM h_hashableAud_raw h_val_eq Iff.rfl
  step h_hashableAud_term as hashableAud

  -- `privateAudValHashed`: the byte bound holds unconditionally, whichever branch `privateAudVal`
  -- took — `encodeV` bytes are always `< 256`, and masking one by `0`/`1` keeps it so.
  have h_byteBoundAud : ∀ i : Fin MAX_AUD_VALUE_LEN, privateAudVal[i].val < 2 ^ 8 := by
    intro i
    simp only [privateAudVal]
    split
    · exact FString.encodeV_val_lt i.isLt
    · simp [Vector.getElem_replicate]
  have h_data_for_input :
      Converts FVec.conversion hashableAud_state
        (⟨hashableAud_result, audValue.len⟩ : FString bn254 MAX_AUD_VALUE_LEN).data privateAudVal :=
    h_hashableAud
  have h_len0 := FString.converts_len h_audValue
  have h_len_for_input :
      Converts F.conversion hashableAud_state
        (⟨hashableAud_result, audValue.len⟩ : FString bn254 MAX_AUD_VALUE_LEN).len
        (audValue_val.length : ZMod bn254) :=
    h_len0
  have h_privateAudValHashed_term := convertsM_of_convertsM
    (HashToField.hashBytesToField.convertsM h_H h_data_for_input h_len_for_input (by decide))
    rfl (iff_true_intro h_byteBoundAud)
  step h_privateAudValHashed_term as privateAudValHashed

  -- `uidValueHashed`.
  have h_byteBoundUidValue : ∀ i : Fin MAX_UID_VALUE_LEN, uidValue_vals[i].val < 2 ^ 8 := by
    simp only [uidValue_vals]
    exact fun i ↦ FString.encodeV_val_lt i.isLt
  have h_uidValueHashed_term := convertsM_of_convertsM
    (HashToField.hashBytesToField.convertsM h_H (FString.converts_data h_uidValue)
      (FString.converts_len h_uidValue) (by decide))
    rfl (iff_true_intro h_byteBoundUidValue)
  step h_uidValueHashed_term as uidValueHashed

  -- `uidNameHashed`.
  have h_byteBoundUidName : ∀ i : Fin MAX_UID_NAME_LEN, uidName_vals[i].val < 2 ^ 8 := by
    simp only [uidName_vals]
    exact fun i ↦ FString.encodeV_val_lt i.isLt
  have h_uidNameHashed_term := convertsM_of_convertsM
    (HashToField.hashBytesToField.convertsM h_H (FString.converts_data h_uidName)
      (FString.converts_len h_uidName) (by decide))
    rfl (iff_true_intro h_byteBoundUidName)
  step h_uidNameHashed_term as uidNameHashed

  -- The final Poseidon call, with `Computes H` applied to the assembled input vector.
  have h_inputVec := FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push FVec.converts_empty h_pepper) h_privateAudValHashed) h_uidValueHashed)
    h_uidNameHashed
  exact convertsM_of_convertsM (h_H (by decide) (by decide) h_inputVec) rfl (by simp)

end computeIdentityCommitment
