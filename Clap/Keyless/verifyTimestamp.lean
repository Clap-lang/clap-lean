import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Keyless.Input

open Clap Lang FString FArray Primes

/-- CIRCOM uses `LessThan(252)` for the comparison. We use 64-bit (`F.lessThan 64`)
    instead because Unix timestamps are seconds since 1970-01-01 and fit comfortably
    in 64 bits (`2^64 ≈ 5.8 × 10^{17}` seconds, i.e., ~18 billion years). Even with
    a generous `expHorizon`, the sum `iat + expHorizon` cannot overflow 64 bits for
    any realistic timestamp. Using 64 bits produces fewer constraints than 252.

    NOTE: CIRCOM checks `expDate < iat + expHorizon`, meaning the expiration
    date must fall before issued-at + horizon. AIP-061 describes this differently
    as `iat < expDate + expHorizon`. We follow CIRCOM as source of truth. -/
def verifyTimestamp (iatValue : FString bn254 MAX_IAT_VALUE_LEN)
  (expDate expHorizon : F bn254) :
  ClapM bn254 Unit
:= do
  let iatScalar ← FString.asciiDigitsToScalar iatValue
  -- 64-bit comparison suffices for timestamps (CIRCOM uses 252 bits)
  assert (← lessThan 64 expDate (← iatScalar + expHorizon))


namespace verifyTimestamp

lemma convertsM
  {state : ClapMState bn254}
  {iatValue : FString bn254 MAX_IAT_VALUE_LEN}
  {iatValue_vals : Vector (ZMod bn254) MAX_IAT_VALUE_LEN}
  {expDate expHorizon : F bn254}
  {expDate_val expHorizon_val : ZMod bn254}
  {len_val : ZMod bn254}
  -- Separate `Converts` hypotheses for `data` and `len`
  -- as in `asciiDigitsToScalar.convertsM`
  (h_data : Converts FVec.conversion state iatValue.data iatValue_vals)
  (h_len : Converts F.conversion state iatValue.len len_val)
  (h_expDate : Converts F.conversion state expDate expDate_val)
  (h_expHorizon : Converts F.conversion state expHorizon expHorizon_val) :
  -- Define `iatScalar` here so we can use it in the conclusion as well.
  let iatScalar := asciiDigitsToScalar.value iatValue_vals len_val.val
  expDate_val.val < 2 ^ 64 →
  iatScalar.val + expHorizon_val.val < 2 ^ 64 →
  ConvertsM FUnit.conversion (verifyTimestamp iatValue expDate expHorizon) state ()
    ((∀ i : Fin MAX_IAT_VALUE_LEN,
        i.val < len_val.val →
          48 ≤ iatValue_vals[i].val ∧ iatValue_vals[i].val ≤ 57
      ) ∧
      0 < len_val.val ∧ len_val.val < MAX_IAT_VALUE_LEN ∧
      (∀ i : Fin MAX_IAT_VALUE_LEN, iatValue_vals[i].val < 2 ^ 8) ∧
      expDate_val.val < (iatScalar + expHorizon_val).val
    )
:= by
  intro iatScalar h64a h64b
  unfold verifyTimestamp
  have hAsc := asciiDigitsToScalar.convertsM h_data h_len (by decide) (by decide) (by decide)
  have h_expDate1 := converts_skip hAsc h_expDate
  have h_expHorizon1 := converts_skip hAsc h_expHorizon
  refine convertsM_of_convertsM
    (convertsM_bind_and (constraints2 := expDate_val.val < (iatScalar + expHorizon_val).val)
      hAsc ?_) rfl ?_
  · have h_iatScalar := hAsc.result
    clear h_data h_len h_expDate h_expHorizon hAsc
    -- Make the gadget's result/state opaque: left as terms, the `step`s below unfold
    -- `asciiDigitsToScalar` through its concrete width and time out in `whnf`.
    generalize iatValue.asciiDigitsToScalar.getResult state.numAlloc state.σ = ascRef at *
    generalize iatValue.asciiDigitsToScalar.getState state = ascState at *
    step mkAdd.convertsM h_iatScalar h_expHorizon1 as t1
    have h64p : (2 : ℕ) ^ 64 < bn254 := by decide
    have hb : (iatScalar + expHorizon_val).val < 2 ^ 64 := by
      rw [ZMod.val_add_of_lt (by omega)]
      omega
    step lessThan.convertsM h_expDate1 h_t1 h64a hb (by decide) as t2
    apply convertsM_of_convertsM (assert.convertsM h_t2)
    · rfl
    · simp only [true_implies, decide_eq_true_eq]
      rfl
  · have hmax : MAX_IAT_VALUE_LEN = 45 := rfl
    constructor
    · rintro ⟨⟨h_digits, h_len0, h_lenw, h_bytes⟩, h_cmp⟩
      exact ⟨h_digits, h_len0, by omega, h_bytes, h_cmp⟩
    · rintro ⟨h_digits, h_len0, h_lenw, h_bytes, h_cmp⟩
      exact ⟨⟨h_digits, h_len0, by omega, h_bytes⟩, h_cmp⟩

lemma convertsM_string
  {state : ClapMState bn254}
  {iatValue : FString bn254 MAX_IAT_VALUE_LEN}
  {s : String}
  {expDate expHorizon : F bn254}
  {expDate_val expHorizon_val : ZMod bn254}
  (h_iat : Converts FString.conversion state iatValue s)
  (h_s_len : s.length ≤ MAX_IAT_VALUE_LEN)
  (h_chars : ∀ c ∈ s.toList, c.toNat < 256)
  (h_expDate : Converts F.conversion state expDate expDate_val)
  (h_expHorizon : Converts F.conversion state expHorizon expHorizon_val) :
  -- Define `iatScalar` here so we can use it in the conclusion as well.
  let iatScalar :=
    asciiDigitsToScalar.value (encodeV MAX_IAT_VALUE_LEN s) s.length
  expDate_val.val < 2 ^ 64 →
  iatScalar.val + expHorizon_val.val < 2 ^ 64 →
  ConvertsM FUnit.conversion (verifyTimestamp iatValue expDate expHorizon) state ()
    ( (∀ c ∈ s.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
      0 < s.length ∧ s.length < MAX_IAT_VALUE_LEN ∧
      -- The byte-range conjunct is dropped: `FString.conversion`'s `encodeV` always
      -- produces bytes (`c.toUInt8.toNat < 256`), so it holds unconditionally here.
      expDate_val.val < (iatScalar + expHorizon_val).val
    )
:= by
  intro iatScalar h64a h64b
  unfold verifyTimestamp
  have hAsc0 := asciiDigitsToScalar.convertsM_string h_iat h_s_len h_chars
    (by decide) (by decide) (by decide)
  have hAsc := convertsM_of_convertsM hAsc0
    (by split
        · rename_i h; exact (asciiDigitsToScalar.value_encodeV h.1 h.2.1 h.2.2).symm
        · rfl)
    Iff.rfl
  have h_expDate1 := converts_skip hAsc h_expDate
  have h_expHorizon1 := converts_skip hAsc h_expHorizon
  refine convertsM_of_convertsM
    (convertsM_bind_and (constraints2 := expDate_val.val < (iatScalar + expHorizon_val).val)
      hAsc ?_) rfl ?_
  · have h_iatScalar := hAsc.result
    clear h_iat h_s_len h_chars h_expDate h_expHorizon hAsc hAsc0
    -- Make the gadget's result/state opaque: left as terms, the `step`s below unfold
    -- `asciiDigitsToScalar` through its concrete width and time out in `whnf`.
    generalize iatValue.asciiDigitsToScalar.getResult state.numAlloc state.σ = ascRef at *
    generalize iatValue.asciiDigitsToScalar.getState state = ascState at *
    step mkAdd.convertsM h_iatScalar h_expHorizon1 as t1
    have h64p : (2 : ℕ) ^ 64 < bn254 := by decide
    have hb : (iatScalar + expHorizon_val).val < 2 ^ 64 := by
      rw [ZMod.val_add_of_lt (by omega)]
      omega
    step lessThan.convertsM h_expDate1 h_t1 h64a hb (by decide) as t2
    apply convertsM_of_convertsM (assert.convertsM h_t2)
    · rfl
    · simp only [true_implies, decide_eq_true_eq]
      rfl
  · have hmax : MAX_IAT_VALUE_LEN = 45 := rfl
    constructor
    · rintro ⟨⟨h_len0, h_lenw, h_digits⟩, h_cmp⟩
      exact ⟨h_digits, h_len0, by omega, h_cmp⟩
    · rintro ⟨h_digits, h_len0, h_lenw, h_cmp⟩
      exact ⟨⟨h_len0, by omega, h_digits⟩, h_cmp⟩

end verifyTimestamp
