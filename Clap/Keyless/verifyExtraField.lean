import Clap.Lang.Core.FB.not
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon
import Clap.Lang.Core.FB.assertBool
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Core.FB.conditionallyAssert
import Clap.RandomOracle.HashFn

import Clap.Lang.Data.FString.isSubstring

open Clap Lang FString FArray Primes Poseidon RandomOracle

/-- Verify the extra field (optional). -/
def verifyExtraField (json : JSONStructure bn254)
  (extra : ExtraFieldInput bn254) :
  ClapM bn254 Unit
:= do
  -- useExtraField must be boolean
  FB.assertBool extra.useExtraField
  -- Check substring
  let efPasses ←
    FString.isSubstring (by decide) json.payload.data json.payloadHash
      extra.extraField
      extra.extraFieldIndex
  -- Assert not inside nested brackets
  enforceNotNested extra.extraFieldIndex extra.extraField.len json.bracketsDepthMap
  FB.conditionallyAssert extra.useExtraField efPasses
  -- Assert extra field does not start inside a string body
  -- CIRCOM: ef_start_char === 0
  eq0 (← selectArrayValue _ json.stringBodies.data extra.extraFieldIndex)

namespace verifyExtraField

-- Poseidon sits beneath `isSubstring`'s hash challenge, as in `verifyUnquotedField.lean` /
-- `verifyEvField.lean` / `verifyQuotedField.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- `extra.useExtraField` is a raw top-level `F bn254` input with no upstream invariant: nothing
guarantees `useExtra_val ∈ {0,1}` before `FB.assertBool` runs. So `FB.conditionallyAssert`'s own
`convertsM` (which needs a genuine `Converts FB.conversion` fact on its antecedent — a fact with
*no witness at all* once `useExtra_val ∉ {0,1}`) cannot be applied directly. This is an unpublished
"unchecked" variant of `conditionallyAssert`, proved by going underneath it to raw field
arithmetic: `conditionallyAssert a c := do let nc ← not c; let conj ← and a nc; eq0 conj`, and
both `not`/`and` are themselves thin wrappers over `mkSub`/`mkMul`, which need no booleanity at
all. The constraint below is *always* true of the real gate-level circuit, for any `a_val`
whatsoever — `conditionallyAssertOfF_bridge` below relates it to the nice form once `a_val` is
known boolean. -/
private lemma conditionallyAssertOfF
  {state : ClapMState bn254}
  {antecedent : F bn254} {a_val : ZMod bn254}
  (h_a : Converts F.conversion state antecedent a_val)
  {consequent : FB bn254} {c_val : Bool}
  (h_c : Converts FB.conversion state consequent c_val)
:
  ConvertsM FUnit.conversion (FB.conditionallyAssert antecedent consequent) state ()
    (a_val * (if !c_val then (1 : ZMod bn254) else 0) = 0)
:= by
  unfold FB.conditionallyAssert
  step not.convertsM h_c as nc
  have h_nc_f := F.converts_of_FB_converts h_nc
  unfold FB.and
  step mkMul.convertsM h_a h_nc_f as conj
  apply convertsM_of_convertsM (eq0.convertsM h_conj)
  · rfl
  · simp only [true_implies]

/-- Once `a_val` is known boolean (established by the earlier `FB.assertBool` stage), the raw
constraint above is equivalent to the honest `conditionallyAssert` reading. -/
private lemma conditionallyAssertOfF_bridge
  {a_val : ZMod bn254} (h1 : a_val = 0 ∨ a_val = 1) (c_val : Bool)
:
  (a_val * (if !c_val then (1 : ZMod bn254) else 0) = 0) ↔ (a_val = 1 → c_val = true)
:= by rcases h1 with rfl | rfl <;> cases c_val <;> simp

/-- Bridges `selectArrayValue`/`eq0`'s raw `ZMod`-mapped constraint (what `selectArrayValue`
literally computes over the `FVec`-converted bit vector) to the cleaner `Bool`-vector form the
public statement below uses. -/
private lemma getD_map_ite_eq_zero_iff {n : ℕ} (v : Vector Bool n) (i : ℕ) :
  (v.map fun b ↦ if b then (1 : ZMod bn254) else 0).getD i 0 = 0 ↔ v.getD i false = false
:= by
  simp only [Vector.getD, Array.getD_eq_getD_getElem?, Vector.toArray_map, Array.getElem?_map]
  cases h : v.toArray[i]? with
  | none => simp
  | some b => cases b <;> simp

/-- The four-stage tail behind `verifyExtraField` *after* `FB.assertBool`, stated over fully
abstract actions, known only via their `ConvertsM` facts — never through `isSubstring` /
`enforceNotNested` / `FB.conditionallyAssert` / `selectArrayValue`/`eq0` by name. `action4` is a
curried function of `action2`'s result (`efPasses`), instantiated at the call site as
`fun x ↦ FB.conditionallyAssert extra.useExtraField x` — `extra.useExtraField` itself is not
threaded through here at all, since (unlike `verifyEvField`'s two value-producing stages) it is a
fixed top-level input, not a prior stage's result. Same trick as `verifyEvField.bind_convertsM` /
`verifyQuotedField.bind_convertsM`, kept to stages 2–5 only: stage 1 (`assertBool`) is combined
separately via `convertsM_bind_guard`, since its constraint is exactly what makes stage 4 provable
in its nice form. -/
private lemma tail_convertsM
  {state : ClapMState bn254}
  {action2 : ClapM bn254 (FB bn254)} {val2 : Bool} {C2 : Prop}
  (h2 : ConvertsM FB.conversion action2 state val2 C2)
  {action3 : ClapM bn254 Unit} {C3 : Prop}
  (h3 : ConvertsM FUnit.conversion action3 (action2.getState state) () C3)
  {action4 : FB bn254 → ClapM bn254 Unit} {C4 : Prop}
  (h4 : ConvertsM FUnit.conversion (action4 (action2.getResult state.numAlloc state.σ))
          (action3.getState (action2.getState state)) () C4)
  {action5 : ClapM bn254 Unit} {C5 : Prop}
  (h5 : ConvertsM FUnit.conversion action5
          ((action4 (action2.getResult state.numAlloc state.σ)).getState
            (action3.getState (action2.getState state))) () C5)
:
  ConvertsM FUnit.conversion
    (do
      let efPasses ← action2
      action3
      action4 efPasses
      action5)
    state () (C2 ∧ C3 ∧ C4 ∧ C5)
:= convertsM_bind_and h2 (convertsM_bind_and h3 (convertsM_bind_and h4 h5))

lemma convertsM {H : HashFn} (h_H : Computes H) {state : ClapMState bn254}
  {extra : ExtraFieldInput bn254}
  {json  : JSONStructure bn254}
  -- Ideal values
  {payload_val : String}
  {stringBodies_val     : Vector Bool MAX_JWT_PAYLOAD_LEN}
  {bracketsDepthMap_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN}
  {extra_vals           : Vector (ZMod bn254) MAX_EXTRA_FIELD_KV_PAIR_LEN}
  {payloadHash_val useExtra_val extraFieldIndex_val extra_len : ZMod bn254}
  -- `json` conversion lemmas
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion       state json.payloadHash payloadHash_val)
  (h_stringBodies     : Converts FArray.conversion  state json.stringBodies.data stringBodies_val)
  (h_bracketsDepthMap : Converts FVec.conversion    state json.bracketsDepthMap bracketsDepthMap_val)
  -- `extra` conversion lemmas
  (h_extra_data      : Converts FVec.conversion state extra.extraField.data extra_vals)
  (h_extra_len       : Converts F.conversion    state extra.extraField.len extra_len)
  (h_use_extra       : Converts F.conversion    state extra.useExtraField useExtra_val)
  (h_extraFieldIndex : Converts F.conversion    state extra.extraFieldIndex extraFieldIndex_val) :
  let payloadV := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  ConvertsM FUnit.conversion (verifyExtraField json extra) state
    ()
    ( -- From `FB.assertBool`
      (useExtra_val = 0 ∨ useExtra_val = 1) ∧
      -- From `isSubstring.convertsM`
      ( (∀ i : Fin MAX_EXTRA_FIELD_KV_PAIR_LEN, extra_vals[i].val < 2 ^ 8) ∧
        (extraFieldIndex_val + extra_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        extraFieldIndex_val.val < MAX_JWT_PAYLOAD_LEN ∧
        extraFieldIndex_val.val < (extraFieldIndex_val + extra_len).val
      ) ∧
      -- From `enforceNotNested.convertsM` (its three range conjuncts duplicate the block above)
      (bracketsDepthMap_val.extract extraFieldIndex_val.val
        (extraFieldIndex_val + extra_len).val
      ).sum = 0 ∧
      -- From `FB.conditionallyAssert`
      (useExtra_val = 1 →
        FString.isSubstring.accepts H payloadV payloadHash_val extra_vals extra_len
          extraFieldIndex_val
      ) ∧
      -- From `selectArrayValue`/`eq0` — CIRCOM: ef_start_char === 0
      ( extraFieldIndex_val.val < MAX_JWT_PAYLOAD_LEN ∧
        stringBodies_val.getD extraFieldIndex_val.val false = false
      )
    )
:= by
  intro payloadV
  have h_n_bn254 : MAX_JWT_PAYLOAD_LEN < bn254 := by decide
  have hw_minBits : 2 ^ (minBits' MAX_JWT_PAYLOAD_LEN + 1) < bn254 := by
    have h11 : minBits' MAX_JWT_PAYLOAD_LEN ≤ 11 := by
      unfold minBits'
      split
      · omega
      · rename_i hx
        have hx11 : MAX_JWT_PAYLOAD_LEN < 2 ^ 11 := by decide
        have := (Nat.log2_lt hx).mpr hx11
        omega
    have h2 : (2:ℕ) ^ (minBits' MAX_JWT_PAYLOAD_LEN + 1) ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4096 : (2:ℕ) ^ 12 < bn254 := by decide
    omega
  unfold verifyExtraField

  -- Stage 1: `FB.assertBool extra.useExtraField`.
  have h1 := FB.assertBool.convertsM h_use_extra
  replace h_payload := converts_skip h1 h_payload
  replace h_payloadHash := converts_skip h1 h_payloadHash
  replace h_stringBodies := converts_skip h1 h_stringBodies
  replace h_bracketsDepthMap := converts_skip h1 h_bracketsDepthMap
  replace h_extra_data := converts_skip h1 h_extra_data
  replace h_extra_len := converts_skip h1 h_extra_len
  replace h_use_extra := converts_skip h1 h_use_extra
  replace h_extraFieldIndex := converts_skip h1 h_extraFieldIndex

  -- Stage 2: `isSubstring`.
  have h2 := FString.isSubstring.convertsM h_H (by decide)
    (FString.converts_data h_payload) h_payloadHash h_extra_data h_extra_len h_extraFieldIndex
    (by decide) h_n_bn254 hw_minBits
  replace h_payload := converts_skip h2 h_payload
  replace h_payloadHash := converts_skip h2 h_payloadHash
  replace h_stringBodies := converts_skip h2 h_stringBodies
  replace h_bracketsDepthMap := converts_skip h2 h_bracketsDepthMap
  replace h_extra_data := converts_skip h2 h_extra_data
  replace h_extra_len := converts_skip h2 h_extra_len
  replace h_use_extra := converts_skip h2 h_use_extra
  replace h_extraFieldIndex := converts_skip h2 h_extraFieldIndex

  -- Stage 3: `enforceNotNested`.
  have h3 := enforceNotNested.convertsM h_extraFieldIndex h_extra_len h_bracketsDepthMap
    h_n_bn254 hw_minBits
  replace h_stringBodies := converts_skip h3 h_stringBodies
  replace h_extra_data := converts_skip h3 h_extra_data
  replace h_extra_len := converts_skip h3 h_extra_len
  replace h_use_extra := converts_skip h3 h_use_extra
  replace h_extraFieldIndex := converts_skip h3 h_extraFieldIndex

  -- Stage 4: `FB.conditionallyAssert extra.useExtraField efPasses`, unchecked (raw antecedent).
  have h4 := conditionallyAssertOfF h_use_extra (converts_skip h3 h2.result)
  replace h_stringBodies := converts_skip h4 h_stringBodies
  replace h_extraFieldIndex := converts_skip h4 h_extraFieldIndex

  -- Stage 5: `selectArrayValue` then `eq0` — a two-assertion bind, combined directly (both
  -- concrete, adjacent — same shape as `poseidonAssertTail`'s own two-stage combination).
  have h5a := selectArrayValue.convertsM h_extraFieldIndex
    (FVec.converts_of_FArray_converts h_stringBodies) h_n_bn254
  have h5 := convertsM_bind_and h5a (eq0.convertsM h5a.result)

  have hTail := tail_convertsM h2 h3 h4 h5

  -- Combine stage 1 with the tail: `assertBool`'s constraint guards stage 4's nice reading, and
  -- is threaded past stages 2–3 (unchanged) and stage 5 (bridged separately) to reach it.
  -- `constraints2'` is spelled out explicitly (matching the public statement's tail verbatim) so
  -- it is pinned down *before* the guard is proved, rather than left as a metavariable for
  -- `constructor`/`exact` to infer (which gets stuck, since an anonymous constructor needs its
  -- expected type known in advance).
  refine convertsM_of_convertsM
    (convertsM_bind_guard (constraints2' :=
      ( (∀ i : Fin MAX_EXTRA_FIELD_KV_PAIR_LEN, extra_vals[i].val < 2 ^ 8) ∧
        (extraFieldIndex_val + extra_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        extraFieldIndex_val.val < MAX_JWT_PAYLOAD_LEN ∧
        extraFieldIndex_val.val < (extraFieldIndex_val + extra_len).val
      ) ∧
      (bracketsDepthMap_val.extract extraFieldIndex_val.val
        (extraFieldIndex_val + extra_len).val
      ).sum = 0 ∧
      (useExtra_val = 1 →
        FString.isSubstring.accepts H payloadV payloadHash_val extra_vals extra_len
          extraFieldIndex_val
      ) ∧
      ( extraFieldIndex_val.val < MAX_JWT_PAYLOAD_LEN ∧
        stringBodies_val.getD extraFieldIndex_val.val false = false
      ))
      h1 hTail ?_)
    rfl Iff.rfl
  intro h1c
  constructor
  · rintro ⟨hc2, hc3, hc4, hc5⟩
    exact ⟨hc2, hc3.2.2.2, (conditionallyAssertOfF_bridge h1c _).mp hc4, hc5.1,
      (getD_map_ite_eq_zero_iff _ _).mp hc5.2⟩
  · rintro ⟨hc2, hcE, hc4nice, hc5a, hc5b⟩
    obtain ⟨hAbyte, hw1, hw2, hw3⟩ := hc2
    exact ⟨⟨hAbyte, hw1, hw2, hw3⟩, ⟨hw1, hw2, hw3, hcE⟩,
      (conditionallyAssertOfF_bridge h1c _).mpr hc4nice,
      hc5a, (getD_map_ite_eq_zero_iff _ _).mpr hc5b⟩

end verifyExtraField
