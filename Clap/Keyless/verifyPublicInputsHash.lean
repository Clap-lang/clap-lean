import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.bracketsMap
import Clap.Lang.Data.JWT.bracketsDepthMap
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.HashToField.hash64BitLimbsToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray Primes HashToField Poseidon RandomOracle

/-- Compute and verify the public inputs hash.
    Collects all verifier-facing data and checks it matches `declaredHash`. -/
def verifyPublicInputsHash
    (idc : F bn254)
    (commit : CommitmentInput bn254)
    (rsa : RSAInput bn254)
    (issValue : FString bn254 MAX_ISS_VALUE_LEN)
    (extra : ExtraFieldInput bn254)
    (audOverride : AudOverrideInput bn254)
    (jwtHeader : FString bn254 MAX_B64U_JWT_HEADER_W_DOT_LEN)
    (declaredHash : F bn254) :
    ClapM bn254 Unit
  := do
  -- Hash components
  let hashedIssValue ← hashBytesToField issValue
  let hashedExtraField ← hashBytesToField extra.extraField
  let hashedJwtHeader ← hashBytesToField jwtHeader
  -- CIRCOM: Hash64BitLimbsToFieldWithLen(32)(pubkey_modulus_tagged, 256)
  -- 256 = RSA_KEY_BYTES = 32 limbs * 8 bytes/limb
  let hashedPubkeyModulus ←
    hash64BitLimbsToField {data := rsa.pubkeyModulus, len := ← mkF RSA_KEY_BYTES}
  let overrideAudValHashed ← hashBytesToField audOverride.overrideAudValue
  -- Poseidon(14 inputs) in the exact order from CIRCOM
  let computed ← poseidonBN254
    #v[ commit.epk[0], commit.epk[1], commit.epk[2], commit.epkLen
    , idc
    , commit.expDate
    , commit.expHorizon
    , hashedIssValue
    , extra.useExtraField
    , hashedExtraField
    , hashedJwtHeader
    , hashedPubkeyModulus
    , overrideAudValHashed
    , audOverride.useAudOverride
    ]
  assert_eq computed declaredHash

namespace verifyPublicInputsHash

open Poseidon RandomOracle Primes

-- Poseidon is opaque to this proof, as in `verifyEvField.lean` / `verifyQuotedField.lean` /
-- `computeIdentityCommitment.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- The Poseidon(14) call plus the closing `assert_eq`, factored out of `convertsM` so this
chain's proof term is checked on its own rather than as part of one 8-stage combination — doing
it inline needs `set_option maxHeartbeats` several times over the default; split out like this,
the whole file fits in the default budget. Same trick as `verifyEvField.bind_convertsM` /
`verifyQuotedField.bind_convertsM`, just over the circuit-level refs directly rather than over
abstract actions, since the cost here is term size, not whnf-unfolding concrete gadgets. -/
private lemma poseidonAssertTail
  {H : HashFn} (h_H : Computes H)
  {state : ClapMState bn254}
  {declaredHash : F bn254} {declaredHash_val : ZMod bn254}
  {epkA epkB epkC epkLen idcE expDateE expHorizonE issE useExtraE extraE jwtE pkE audE useAudE :
    F bn254}
  {epk_valsA epk_valsB epk_valsC epkLen_val idc_val expDate_val expHorizon_val
    hashedIssValue useExtra_val hashedExtraField hashedJwtHeader hashedPubkeyModulus
    overrideAudValHashed useAudOverride_val : ZMod bn254}
  (h_epk0 : Converts F.conversion state epkA epk_valsA)
  (h_epk1 : Converts F.conversion state epkB epk_valsB)
  (h_epk2 : Converts F.conversion state epkC epk_valsC)
  (h_epkLen : Converts F.conversion state epkLen epkLen_val)
  (h_idc : Converts F.conversion state idcE idc_val)
  (h_expDate : Converts F.conversion state expDateE expDate_val)
  (h_expHorizon : Converts F.conversion state expHorizonE expHorizon_val)
  (hIss : Converts F.conversion state issE hashedIssValue)
  (h_use_extra : Converts F.conversion state useExtraE useExtra_val)
  (hExtra : Converts F.conversion state extraE hashedExtraField)
  (hJwt : Converts F.conversion state jwtE hashedJwtHeader)
  (hPk : Converts F.conversion state pkE hashedPubkeyModulus)
  (hAud : Converts F.conversion state audE overrideAudValHashed)
  (h_aud2 : Converts F.conversion state useAudE useAudOverride_val)
  (h_declaredHash : Converts F.conversion state declaredHash declaredHash_val) :
  ConvertsM FUnit.conversion
    (poseidonBN254 #v[epkA, epkB, epkC, epkLen, idcE, expDateE, expHorizonE, issE, useExtraE,
      extraE, jwtE, pkE, audE, useAudE] >>= fun computed => assert_eq computed declaredHash)
    state ()
    (True ∧ H #v[epk_valsA, epk_valsB, epk_valsC, epkLen_val, idc_val, expDate_val, expHorizon_val,
      hashedIssValue, useExtra_val, hashedExtraField, hashedJwtHeader, hashedPubkeyModulus,
      overrideAudValHashed, useAudOverride_val] = declaredHash_val)
:= by
  have hVec14 := FVec.converts_push (FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push (FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push (FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push (FVec.converts_push FVec.converts_empty h_epk0) h_epk1) h_epk2) h_epkLen)
    h_idc) h_expDate) h_expHorizon) hIss) h_use_extra) hExtra) hJwt) hPk) hAud) h_aud2
  have hG := h_H (by decide) (by decide) hVec14
  exact convertsM_bind_and hG (assert_eq.convertsM hG.result (converts_skip hG h_declaredHash))

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  {idc : F bn254}
  {iss : FString bn254 MAX_ISS_VALUE_LEN}
  {extra : ExtraFieldInput bn254}
  {jwtHeader : FString bn254 MAX_B64U_JWT_HEADER_W_DOT_LEN}
  {rsa : RSAInput bn254}
  {audOverride : AudOverrideInput bn254}
  {commit : CommitmentInput bn254}
  {declaredHash : F bn254}
  -- Ideal values
  {iss_vals : Vector (ZMod bn254) MAX_ISS_VALUE_LEN}
  {extra_vals : Vector (ZMod bn254) MAX_EXTRA_FIELD_KV_PAIR_LEN}
  {pubkeyModulus_val : Vector (ZMod bn254) RSA_NUM_LIMBS}
  {jwtHeader_vals : Vector (ZMod bn254) MAX_B64U_JWT_HEADER_W_DOT_LEN}
  {overrideAud_vals : Vector (ZMod bn254) MAX_AUD_VALUE_LEN}
  {iss_len extra_len jwtHeader_len overrideAud_len declaredHash_val useAudOverride_val : ZMod bn254}
  {epk_vals : Vector (ZMod bn254) EPK_NUM_FIELDS}
  {epkLen_val expDate_val expHorizon_val idc_val useExtra_val : ZMod bn254}
  (h_aud₁       : Converts FVec.conversion state audOverride.overrideAudValue.data overrideAud_vals)
  (h_aud_len    : Converts F.conversion state audOverride.overrideAudValue.len overrideAud_len)
  (h_aud₂       : Converts F.conversion state audOverride.useAudOverride useAudOverride_val)
  (h_epk        : Converts FVec.conversion state commit.epk epk_vals)
  (h_epkLen     : Converts F.conversion state commit.epkLen epkLen_val)
  (h_expDate    : Converts F.conversion state commit.expDate expDate_val)
  (h_expHorizon : Converts F.conversion state commit.expHorizon expHorizon_val)
  (h_idc        : Converts F.conversion state idc idc_val)
  (h_use_extra  : Converts F.conversion state extra.useExtraField useExtra_val)
  -- Conversion lemmas
  (h_iss_data : Converts FVec.conversion state iss.data iss_vals)
  (h_iss_len : Converts F.conversion state iss.len iss_len)
  (h_extra_data : Converts FVec.conversion state extra.extraField.data extra_vals)
  (h_extra_len : Converts F.conversion state extra.extraField.len extra_len)
  (h_jwtHeader_data : Converts FVec.conversion state jwtHeader.data jwtHeader_vals)
  (h_jwtHeader_len : Converts F.conversion state jwtHeader.len jwtHeader_len)
  (h_rsa : Converts FVec.conversion state rsa.pubkeyModulus pubkeyModulus_val)
  (h_declaredHash : Converts F.conversion state declaredHash declaredHash_val)
  :
  let hashedIssValue := hashBytesToFieldSpec H iss_vals iss_len
  let hashedExtraField := hashBytesToFieldSpec H extra_vals extra_len
  let hashedJwtHeader := hashBytesToFieldSpec H jwtHeader_vals jwtHeader_len
  let hashedPubkeyModulus := hash64BitLimbsToFieldSpec H pubkeyModulus_val RSA_KEY_BYTES
  let overrideAudValHashed := hashBytesToFieldSpec H overrideAud_vals overrideAud_len
  ConvertsM FUnit.conversion (verifyPublicInputsHash idc commit rsa iss extra audOverride jwtHeader declaredHash) state
    ()
    ( (∀ i : Fin MAX_ISS_VALUE_LEN, iss_vals[i].val < 2 ^ 8) ∧
      (∀ i : Fin MAX_EXTRA_FIELD_KV_PAIR_LEN, extra_vals[i].val < 2 ^ 8) ∧
      (∀ i : Fin MAX_B64U_JWT_HEADER_W_DOT_LEN, jwtHeader_vals[i].val < 2 ^ 8) ∧
      (∀ i : Fin MAX_AUD_VALUE_LEN, overrideAud_vals[i].val < 2 ^ 8) ∧
      declaredHash_val =
        H
          #v[ epk_vals[0], epk_vals[1], epk_vals[2], epkLen_val, idc_val,
              expDate_val,
              expHorizon_val,
              hashedIssValue,
              useExtra_val,
              hashedExtraField,
              hashedJwtHeader,
              hashedPubkeyModulus,
              overrideAudValHashed,
              useAudOverride_val
            ]

    )
:= by
  intro hashedIssValue hashedExtraField hashedJwtHeader hashedPubkeyModulus overrideAudValHashed
  unfold verifyPublicInputsHash

  -- The final equality, spelled once so every nested `convertsM_bind_and` can cite it without
  -- repeating the 14-element vector.
  let eqProp : Prop :=
    H #v[ epk_vals[0], epk_vals[1], epk_vals[2], epkLen_val, idc_val, expDate_val, expHorizon_val,
          hashedIssValue, useExtra_val, hashedExtraField, hashedJwtHeader, hashedPubkeyModulus,
          overrideAudValHashed, useAudOverride_val ] = declaredHash_val

  -- Stage A: hash the `iss` value.
  have hA := hashBytesToField.convertsM h_H h_iss_data h_iss_len (by decide)
  refine convertsM_of_convertsM
    (convertsM_bind_and (constraints2 :=
      (∀ i : Fin MAX_EXTRA_FIELD_KV_PAIR_LEN, extra_vals[i].val < 2 ^ 8) ∧
      (∀ i : Fin MAX_B64U_JWT_HEADER_W_DOT_LEN, jwtHeader_vals[i].val < 2 ^ 8) ∧
      True ∧ True ∧
      (∀ i : Fin MAX_AUD_VALUE_LEN, overrideAud_vals[i].val < 2 ^ 8) ∧
      True ∧ eqProp)
      hA ?_) rfl ?_
  · have hIss := hA.result
    replace h_extra_data := converts_skip hA h_extra_data
    replace h_extra_len := converts_skip hA h_extra_len
    replace h_jwtHeader_data := converts_skip hA h_jwtHeader_data
    replace h_jwtHeader_len := converts_skip hA h_jwtHeader_len
    replace h_rsa := converts_skip hA h_rsa
    replace h_aud₁ := converts_skip hA h_aud₁
    replace h_aud_len := converts_skip hA h_aud_len
    replace h_epk := converts_skip hA h_epk
    replace h_epkLen := converts_skip hA h_epkLen
    replace h_expDate := converts_skip hA h_expDate
    replace h_expHorizon := converts_skip hA h_expHorizon
    replace h_idc := converts_skip hA h_idc
    replace h_use_extra := converts_skip hA h_use_extra
    replace h_aud₂ := converts_skip hA h_aud₂
    replace h_declaredHash := converts_skip hA h_declaredHash
    -- Make `hashBytesToField iss`'s result/state opaque: the goal is already fixed to this
    -- exact continuation, so later stages won't need to unfold it to match against it.
    generalize (hashBytesToField iss).getResult state.numAlloc state.σ = rA at *
    generalize (hashBytesToField iss).getState state = sA at *

    -- Stage B: hash the `extra` field.
    have hB := hashBytesToField.convertsM h_H h_extra_data h_extra_len (by decide)
    refine convertsM_bind_and (constraints2 :=
      (∀ i : Fin MAX_B64U_JWT_HEADER_W_DOT_LEN, jwtHeader_vals[i].val < 2 ^ 8) ∧
      True ∧ True ∧
      (∀ i : Fin MAX_AUD_VALUE_LEN, overrideAud_vals[i].val < 2 ^ 8) ∧
      True ∧ eqProp)
      hB ?_
    · have hExtra := hB.result
      replace h_jwtHeader_data := converts_skip hB h_jwtHeader_data
      replace h_jwtHeader_len := converts_skip hB h_jwtHeader_len
      replace h_rsa := converts_skip hB h_rsa
      replace h_aud₁ := converts_skip hB h_aud₁
      replace h_aud_len := converts_skip hB h_aud_len
      replace h_epk := converts_skip hB h_epk
      replace h_epkLen := converts_skip hB h_epkLen
      replace h_expDate := converts_skip hB h_expDate
      replace h_expHorizon := converts_skip hB h_expHorizon
      replace h_idc := converts_skip hB h_idc
      replace h_use_extra := converts_skip hB h_use_extra
      replace h_aud₂ := converts_skip hB h_aud₂
      replace h_declaredHash := converts_skip hB h_declaredHash
      replace hIss := converts_skip hB hIss
      generalize (hashBytesToField extra.extraField).getResult sA.numAlloc sA.σ = rB at *
      generalize (hashBytesToField extra.extraField).getState sA = sB at *

      -- Stage C: hash the `jwtHeader`.
      have hC := hashBytesToField.convertsM h_H h_jwtHeader_data h_jwtHeader_len (by decide)
      refine convertsM_bind_and (constraints2 :=
        True ∧ True ∧
        (∀ i : Fin MAX_AUD_VALUE_LEN, overrideAud_vals[i].val < 2 ^ 8) ∧
        True ∧ eqProp)
        hC ?_
      · have hJwt := hC.result
        replace h_rsa := converts_skip hC h_rsa
        replace h_aud₁ := converts_skip hC h_aud₁
        replace h_aud_len := converts_skip hC h_aud_len
        replace h_epk := converts_skip hC h_epk
        replace h_epkLen := converts_skip hC h_epkLen
        replace h_expDate := converts_skip hC h_expDate
        replace h_expHorizon := converts_skip hC h_expHorizon
        replace h_idc := converts_skip hC h_idc
        replace h_use_extra := converts_skip hC h_use_extra
        replace h_aud₂ := converts_skip hC h_aud₂
        replace h_declaredHash := converts_skip hC h_declaredHash
        replace hIss := converts_skip hC hIss
        replace hExtra := converts_skip hC hExtra
        generalize (hashBytesToField jwtHeader).getResult sB.numAlloc sB.σ = rC at *
        generalize (hashBytesToField jwtHeader).getState sB = sC at *

        -- Stage D: allocate the `RSA_KEY_BYTES` literal (the implicit bind the `do`-notation
        -- inserts for `← mkF RSA_KEY_BYTES` inside the structure literal).
        have hD := mkF.convertsM (p := bn254) (a := (RSA_KEY_BYTES : ZMod bn254)) (state := sC)
        refine convertsM_bind_and (constraints2 :=
          True ∧
          (∀ i : Fin MAX_AUD_VALUE_LEN, overrideAud_vals[i].val < 2 ^ 8) ∧
          True ∧ eqProp)
          hD ?_
        · have hRsaLenFact := hD.result
          replace h_rsa := converts_skip hD h_rsa
          replace h_aud₁ := converts_skip hD h_aud₁
          replace h_aud_len := converts_skip hD h_aud_len
          replace h_epk := converts_skip hD h_epk
          replace h_epkLen := converts_skip hD h_epkLen
          replace h_expDate := converts_skip hD h_expDate
          replace h_expHorizon := converts_skip hD h_expHorizon
          replace h_idc := converts_skip hD h_idc
          replace h_use_extra := converts_skip hD h_use_extra
          replace h_aud₂ := converts_skip hD h_aud₂
          replace h_declaredHash := converts_skip hD h_declaredHash
          replace hIss := converts_skip hD hIss
          replace hExtra := converts_skip hD hExtra
          replace hJwt := converts_skip hD hJwt
          generalize (mkF (RSA_KEY_BYTES : ZMod bn254)).getResult sC.numAlloc sC.σ = rD at *
          generalize (mkF (RSA_KEY_BYTES : ZMod bn254)).getState sC = sD at *

          -- Stage E: hash the RSA public key modulus (64-bit limbs).
          let hInputPV : PaddedVector (F bn254) bn254 RSA_NUM_LIMBS := ⟨rsa.pubkeyModulus, rD⟩
          have hE := hash64BitLimbsToField.convertsM (input := hInputPV) h_H h_rsa hRsaLenFact
            (by decide)
          refine convertsM_bind_and (constraints2 :=
            (∀ i : Fin MAX_AUD_VALUE_LEN, overrideAud_vals[i].val < 2 ^ 8) ∧
            True ∧ eqProp)
            hE ?_
          · have hPk := hE.result
            replace h_aud₁ := converts_skip hE h_aud₁
            replace h_aud_len := converts_skip hE h_aud_len
            replace h_epk := converts_skip hE h_epk
            replace h_epkLen := converts_skip hE h_epkLen
            replace h_expDate := converts_skip hE h_expDate
            replace h_expHorizon := converts_skip hE h_expHorizon
            replace h_idc := converts_skip hE h_idc
            replace h_use_extra := converts_skip hE h_use_extra
            replace h_aud₂ := converts_skip hE h_aud₂
            replace h_declaredHash := converts_skip hE h_declaredHash
            replace hIss := converts_skip hE hIss
            replace hExtra := converts_skip hE hExtra
            replace hJwt := converts_skip hE hJwt
            generalize (hash64BitLimbsToField hInputPV).getResult sD.numAlloc sD.σ = rE at *
            generalize (hash64BitLimbsToField hInputPV).getState sD = sE at *

            -- Stage F: hash the overriding `aud` value.
            have hF := hashBytesToField.convertsM h_H h_aud₁ h_aud_len (by decide)
            refine convertsM_bind_and (constraints2 := True ∧ eqProp) hF ?_
            · have hAud := hF.result
              replace h_epk := converts_skip hF h_epk
              replace h_epkLen := converts_skip hF h_epkLen
              replace h_expDate := converts_skip hF h_expDate
              replace h_expHorizon := converts_skip hF h_expHorizon
              replace h_idc := converts_skip hF h_idc
              replace h_use_extra := converts_skip hF h_use_extra
              replace h_aud₂ := converts_skip hF h_aud₂
              replace h_declaredHash := converts_skip hF h_declaredHash
              replace hIss := converts_skip hF hIss
              replace hExtra := converts_skip hF hExtra
              replace hJwt := converts_skip hF hJwt
              replace hPk := converts_skip hF hPk
              generalize
                (hashBytesToField audOverride.overrideAudValue).getResult sE.numAlloc sE.σ = rF
                at *
              generalize (hashBytesToField audOverride.overrideAudValue).getState sE = sF at *

              -- Stage G+H: the 14-input Poseidon call plus the final equality, factored into
              -- `poseidonAssertTail` so its proof term is checked on its own.
              have h_epk0 := FVec.converts_getElem h_epk (show (0 : ℕ) < EPK_NUM_FIELDS by decide)
              have h_epk1 := FVec.converts_getElem h_epk (show (1 : ℕ) < EPK_NUM_FIELDS by decide)
              have h_epk2 := FVec.converts_getElem h_epk (show (2 : ℕ) < EPK_NUM_FIELDS by decide)
              exact poseidonAssertTail h_H h_epk0 h_epk1 h_epk2 h_epkLen h_idc h_expDate
                h_expHorizon hIss h_use_extra hExtra hJwt hPk hAud h_aud₂ h_declaredHash
  · -- The overall constraint `↔`: strip the `True`s from stages D, E, G and flip the equality.
    constructor
    · rintro ⟨hA', hB', hC', -, -, hF', -, hEq⟩
      exact ⟨hA', hB', hC', hF', hEq.symm⟩
    · rintro ⟨hA', hB', hC', hF', hEq⟩
      exact ⟨hA', hB', hC', trivial, trivial, hF', trivial, hEq.symm⟩

end verifyPublicInputsHash
