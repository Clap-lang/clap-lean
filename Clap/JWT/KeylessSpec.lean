import Mathlib.Data.List.Basic

/-!
# The Aptos Keyless ZK relation

## Abstract Fiat-Shamir

The real circuit locates every field via a Fiat-Shamir. Proving a concrete Fiat-Shamir-based implementation sound is later work.

## Out of scope & later work

* The envelope (JWS) is out of scope; `parse` consumes the already-decoded payload.
* The JWT header's contents and the signature are not interpreted
* The circuit itself is an opaque `Accepts` predicate; instantiating it is future work.
-/

namespace Spec.KeylessSpec

/-! ## Claims -/

/-- A level-0 value -/
inductive RawValue where
  | str (s : String)
  | num (digits : String)
  | bool (b : Bool)
  /-- Validated but uninterpreted (a nested object/array, or any other member the circuit never reads). -/
  | opaque (bytes : String)
deriving Repr, DecidableEq

/-- `email_verified`. The circuit admit four encodings:
`ParseEmailVerifiedField` accepts either a bare JSON boolean or a quoted string;
`EmailVerifiedCheck` then pins the content only when
`uid_key = "email"`, requiring the byte length to be exactly 4 (`true`) or 6 (`"true"`) before
comparing bytes, so `false`/`"false"` can never pass, but the parser still has to be able to read
them, since they can appear in tokens whose `uid_key` isn't `email`. -/
inductive EvValue where
  | jsonBool (b : Bool)
  | quoted (b : Bool)
deriving Repr, DecidableEq

def EvValue.isVerified : EvValue → Bool
  | .jsonBool b => b
  | .quoted b   => b

/-- Byte length of the value. Only `4` and `6` are admitted when `uid_key = "email"`. -/
def EvValue.byteLen : EvValue → Nat
  | .jsonBool true  => 4
  | .jsonBool false => 5
  | .quoted true    => 6
  | .quoted false   => 7

/-- The identifying claim's name any string is accepted but the client-side restricts it to only sub and email.
So we constraint it here -/
inductive UidKey where
  | sub
  | email
deriving Repr, DecidableEq

/-- The literal JWT field name a `UidKey` refers to. -/
def UidKey.fieldName : UidKey → String
  | .sub   => "sub"
  | .email => "email"

/-- The three ways the circuit can be configured to check `aud`. -/
inductive AudMode where
  /-- Match the prover's real `aud_val` against `jwt["aud"]`. -/
  | normal
  /-- Recovery mode: match `override_aud_val` against `jwt["aud"]` instead, and do not tie the IDC
  to any real `aud` value. -/
  | override (val : String)
  /-- `skip_aud_checks`: the `aud` field's grammar check is skipped entirely (its witnesses need
  not correspond to anything in the real payload), and the IDC's `aud` hash input is forced to the
  empty string. -/
  | skipped
deriving Repr, DecidableEq

/-- What the circuit checks, per parse. Only claims at nesting level 0 are extracted; everything
else is parsed (to establish validity) and discarded.

`nonce` and `iat` are `Nat` (already decoded), matching what `AsciiDigitsToScalar` does in-circuit.
`aud` is `Option String` because `skipped` mode exists. `emailVerified` is `Option EvValue`:
`none` means the claim is absent, which is the ordinary case whenever `uid_key ≠ "email"`.

`extra_field` is not a field here. `uid_key` is also not a field: it is an input to `parse`
(the parser searches for that specific key). -/
structure Claims where
  iss           : String
  aud           : Option String
  uidVal        : String
  nonce         : Nat
  iat           : Nat
  emailVerified : Option EvValue
deriving Repr, DecidableEq

/-! ## The abstract (for now) parser -/

section Parser

/-! `parse uidKey jwt` returns every `Claims` value consistent with some choice of occurrence for
each duplicated top-level key in `jwt`, having searched for the identifying claim under the name
`uidKey.fieldName`. `[]` means the payload did not parse (structurally malformed, or a required
claim missing). -/
variable (parse : UidKey → String → List Claims)

/- **DOUBLE-CHECK**
We might not need this below. The parser is assumed to be correct and if it parses the JSON is valid -/

-- def ParserValidates (IsValidJson : String → Prop) : Prop :=
--   ∀ uidKey s c, c ∈ parse uidKey s → IsValidJson s

-- def ParserRejectsMalformed (IsValidJson : String → Prop) : Prop :=
--   ∀ uidKey s, ¬ IsValidJson s → parse uidKey s = []

-- theorem parserValidates_iff_rejectsMalformed (IsValidJson : String → Prop) :
--     ParserValidates parse IsValidJson ↔ ParserRejectsMalformed parse IsValidJson := by
--   constructor
--   · intro h uidKey s hbad
--     cases hp : parse uidKey s with
--     | nil => rfl
--     | cons c cs =>
--       exact absurd (h uidKey s c (by rw [hp]; exact List.mem_cons_self)) hbad
--   · intro h uidKey s c hc
--     by_contra hbad
--     rw [h uidKey s hbad] at hc
--     simp at hc

/- **DOUBLE-CHECK** Same here, the parser is assumed to correctly read only claims at nesting 0. -/
-- /-- Every claim is read from nesting level 0 `ValueAtLevel0 s k v`: "in payload `s`, the
-- member named `k` at nesting level 0 has value `v`" -/
-- def ParserLevel0Only (ValueAtLevel0 : String → String → String → Prop) : Prop :=
--   ∀ uidKey s c, c ∈ parse uidKey s →
--     ValueAtLevel0 s "iss" c.iss ∧
--     (∀ a, c.aud = some a → ValueAtLevel0 s "aud" a) ∧
--     ValueAtLevel0 s uidKey.fieldName c.uidVal

-- /-- The parser fails rather than returning a `Claims` with a placeholder for its two mandatory claims -/
-- def ParserRequiresClaims : Prop :=
--   ∀ uidKey s c, c ∈ parse uidKey s → c.iss ≠ "" ∧ c.uidVal ≠ ""

end Parser

/-! ## Statement, witness, and the abstract (for now) cryptography -/

variable {Epk Jwk Sig Commit : Type}

/-- `w_pub`: the publicly-transmitted half of the witness, in AIP-61's order. -/
structure PubInputs (Epk Jwk Commit : Type) where
  epk        : Epk
  addrIdc    : Commit
  expDate    : Nat
  expHorizon : Nat
  issVal     : String
  /-- Raw `"key":"value"` bytes (or any fragment thereof — see `R9`); never parsed. `none` = the
  deployment is not using one. -/
  extraField : Option String
  header     : String
  jwk        : Jwk
  audMode    : AudMode

/-- `w_priv`: the secret half of the witness, in AIP-61's order. -/
structure PrivInputs (Sig : Type) where
  audVal     : String
  uidKey     : UidKey
  uidVal     : String
  pepper     : Nat
  sigOidc    : Sig
  /-- The decoded/plaintext JSON payload of the JWT. -/
  jwt        : String
  epkBlinder : Nat

/-- The hash functions and signature check the relation is stated over (all opaque). -/
structure Crypto (Epk Jwk Sig Commit : Type) where
  /-- `H_zk`, deriving the public inputs hash from `w_pub`. -/
  Hzk       : PubInputs Epk Jwk Commit → Nat
  /-- `H'(uid_key, uid_val, aud_val; r)`. -/
  Hidc      : String → String → String → Nat → Commit
  /-- `H'(epk, exp_date; ρ)`, the EPK commitment carried in the `nonce` claim. -/
  Hnonce    : Epk → Nat → Nat → Nat
  /-- Verification of `σ_oidc` under `jwk` over the header and payload. -/
  verifySig : Jwk → String → String → Sig → Prop

/-- The `aud_val` fed into the IDC hash: the real value in `normal`/`override` mode, or the
empty string in `skipped` mode -/
def effectiveAudVal (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) : String :=
  match p.audMode with
  | .skipped => ""
  | _        => w.audVal

/-! ## "The relation" -/

section Relation

variable (parse : UidKey → String → List Claims) (κ : Crypto Epk Jwk Sig Commit)
variable (TopLevelSubstring : String → String → Prop)

/-- **Conjunct 1.** Verify that the public inputs hash `pih` is correctly derived from `w_pub` by `H_zk`. -/
def R1PihDerived (pih : Nat) (p : PubInputs Epk Jwk Commit) : Prop :=
  pih = κ.Hzk p

/-- **Conjunct 2.** Assert `iss_val = jwt["iss"]`. -/
def R2IssMatches (p : PubInputs Epk Jwk Commit) (c : Claims) : Prop :=
  p.issVal = c.iss

/-- **Conjunct 3.** If `uid_key = "email"`, assert `jwt["email_verified"]` is present and verified. -/
def R3EmailVerified (w : PrivInputs Sig) (c : Claims) : Prop :=
  w.uidKey = .email → ∃ ev, c.emailVerified = some ev ∧ ev.isVerified = true

/-- **Conjunct 4.** Assert `uid_val = jwt[uid_key]`. `uid_key` itself doesn't need re-checking here:
`parse` already searched under `w.uidKey`, so any `c` it returns is already keyed correctly. -/
def R4UidMatches (w : PrivInputs Sig) (c : Claims) : Prop :=
  w.uidVal = c.uidVal

/-- **Conjunct 5.** Assert `addr_idc = H'(uid_key, uid_val, aud_val; r)`, using
`aud_val` (empty string in `skipped` mode). -/
def R5IdcCorrect (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) : Prop :=
  p.addrIdc = κ.Hidc w.uidKey.fieldName w.uidVal (effectiveAudVal p w) w.pepper

/-- **Conjunct 6.** Assert `jwt["aud"]` matches whichever value the current `AudMode` designates:
the prover's real `aud_val` (`normal`), the override (`override`), or nothing at all (`skipped`). -/
def R6AudMatches (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) (c : Claims) : Prop :=
  match p.audMode with
  | .normal      => c.aud = some w.audVal
  | .override o  => c.aud = some o
  | .skipped     => True

/-- **Conjunct 7.** Assert `jwt["nonce"] = H'(epk, exp_date; ρ)` — the ephemeral-key binding. -/
def R7NonceBinds (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) (c : Claims) : Prop :=
  c.nonce = κ.Hnonce p.epk p.expDate w.epkBlinder

/-- **Conjunct 8.** Assert `exp_date < jwt["iat"] + exp_horizon`. -/
def R8ExpDateBounded (p : PubInputs Epk Jwk Commit) (c : Claims) : Prop :=
  p.expDate < c.iat + p.expHorizon

/-- **Conjunct 9.** Assert the `extra_field` bytes (if any) occur verbatim in the payload, unnested
and outside a quoted string. -/
def R9ExtraFieldMatches (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) : Prop :=
  match p.extraField with
  | none       => True
  | some bytes => TopLevelSubstring w.jwt bytes

/-- **Conjunct 10.** Verify `σ_oidc` under `jwk` over `header` and `jwt`. Opaque (for now), the
verifier hardcodes RSA-2048 PKCS#1-v1.5 over SHA-256 -/
def R10SigVerifies (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) : Prop :=
  κ.verifySig p.jwk p.header w.jwt w.sigOidc

/-- **The keyless ZK relation.** -/
def R (pih : Nat) (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) : Prop :=
  ∃ c : Claims,
    c ∈ parse w.uidKey w.jwt ∧
    R1PihDerived κ pih p ∧
    R2IssMatches p c ∧
    R3EmailVerified w c ∧
    R4UidMatches w c ∧
    R5IdcCorrect κ p w ∧
    R6AudMatches p w c ∧
    R7NonceBinds κ p w c ∧
    R8ExpDateBounded p c ∧
    R9ExtraFieldMatches TopLevelSubstring p w ∧
    R10SigVerifies κ p w

end Relation

/-! ## Connecting to an abstract (for now) Circuit -/

section Equivalence

variable (parse : UidKey → String → List Claims) (κ : Crypto Epk Jwk Sig Commit)
variable (TopLevelSubstring : String → String → Prop)
variable (Accepts : Nat → PubInputs Epk Jwk Commit → PrivInputs Sig → Prop)

/-- The circuit's own claim witnesses agree with a parsed `Claims`. -/
def Correlates (p : PubInputs Epk Jwk Commit) (w : PrivInputs Sig) (c : Claims) : Prop :=
  p.issVal = c.iss ∧
  w.uidVal = c.uidVal ∧
  (match p.audMode with
   | .normal     => c.aud = some w.audVal
   | .override o => c.aud = some o
   | .skipped    => True) ∧
  (w.uidKey = .email → ∃ ev, c.emailVerified = some ev ∧ ev.isVerified = true)

/-! ### The main statements

Circuits are represented bu "Accepts" predicate -/

/-- **Soundness.** If the circuit accepts, the relation holds (security) -/
theorem accepts_sound {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig}
    (_h : Accepts pih p w) : R parse κ TopLevelSubstring pih p w := by
  sorry

/-- **Completeness.** If the relation holds, the circuit accepts -/
theorem accepts_complete {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig}
    (_h : R parse κ TopLevelSubstring pih p w) : Accepts pih p w := by
  sorry

/-- **The final boss** -/
theorem accepts_iff {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig} :
    Accepts pih p w ↔ R parse κ TopLevelSubstring pih p w := by
  sorry

/-- The circuit accepts iff the parser returns some `c` that the witnesses correlate  -/
theorem accepts_iff_parse {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig}
    (_hcrypto : R1PihDerived κ pih p ∧ R5IdcCorrect κ p w ∧
      R9ExtraFieldMatches TopLevelSubstring p w ∧ R10SigVerifies κ p w) :
    Accepts pih p w ↔ ∃ c, c ∈ parse w.uidKey w.jwt ∧ Correlates p w c := by
  sorry

/-- Acceptance entails some parse succeeded. -/
theorem accepts_implies_parses {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig}
    (_h : Accepts pih p w) : parse w.uidKey w.jwt ≠ [] := by
  sorry

/-- **DOUBLE-CHECK** Acceptance entails the payload is well-formed JSON. We may not need this given the parser assumption -/
theorem accepts_implies_valid_json {IsValidJson : String → Prop}
    (_hv : ParserValidates parse IsValidJson)
    {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig}
    (_h : Accepts pih p w) : IsValidJson w.jwt := by
  sorry

/-- `R` entails a successful parse, by construction of the existential. -/
theorem R_implies_parses {pih : Nat} {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig}
    (_h : R parse κ TopLevelSubstring pih p w) : parse w.uidKey w.jwt ≠ [] := by
  sorry

end Equivalence

/-! ## Supporting lemmas -/

section Lemmas

variable (parse : UidKey → String → List Claims) (κ : Crypto Epk Jwk Sig Commit)

/-- The parser's numeric decode agrees with `AsciiDigitsToScalar` if the value fits the field. -/
def ParserDecodesLikeCircuit (fieldOrder : Nat) : Prop :=
  ∀ uidKey s c, c ∈ parse uidKey s → c.iat < fieldOrder ∧ c.nonce < fieldOrder

/-- The `nonce` fits the scalar field. Needed because the circuit permits a 99-digit `nonce`
against a 77-digit BN254 modulus, so two distinct nonce strings can share a field element. -/
def NonceFitsField (c : Claims) (fieldOrder : Nat) : Prop :=
  c.nonce < fieldOrder

/-- **DOUBLE-CHECK** A value that is not at level 0 for the identifying key is never the one `R4` reads.
We may not need this given the parser assumption -/
theorem level0_excludes_nested {ValueAtLevel0 : String → String → String → Prop}
    (hl : ParserLevel0Only parse ValueAtLevel0)
    {uidKey : UidKey} {s : String} {c : Claims} (hc : c ∈ parse uidKey s)
    {nested : String} (hnested : ¬ ValueAtLevel0 s uidKey.fieldName nested) :
    c.uidVal ≠ nested := by
  intro heq
  exact hnested (heq ▸ (hl uidKey s c hc).2.2)

/-- The extra-field bytes carried in the public inputs occur in the payload as `R9` requires. -/
theorem extraField_agrees {TopLevelSubstring : String → String → Prop}
    {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig} {ef : String}
    (h : R9ExtraFieldMatches TopLevelSubstring p w) (hsome : p.extraField = some ef) :
    TopLevelSubstring w.jwt ef := by
  simp [R9ExtraFieldMatches, hsome] at h
  exact h

/-- In `normal` mode the committed `aud` is the JWT's, and it's the prover's real `aud_val`. -/
theorem aud_normal_mode {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig} {c : Claims}
    (h : R6AudMatches p w c) (hnormal : p.audMode = .normal) : c.aud = some w.audVal := by
  simp [R6AudMatches, hnormal] at h
  exact h

theorem aud_override_mode {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig} {c : Claims}
    {ovr : String} (h : R6AudMatches p w c) (hoverride : p.audMode = .override ovr) :
    c.aud = some ovr := by
  simp [R6AudMatches, hoverride] at h
  exact h

/-- In `skipped` mode, `R6` asserts nothing about `c.aud` at all -/
theorem aud_skipped_mode {p : PubInputs Epk Jwk Commit} {w : PrivInputs Sig} {c : Claims}
    (_h : R6AudMatches p w c) (_hskipped : p.audMode = .skipped) : True :=
  trivial

/-- An `email`-keyed identity carries a verified address -/
theorem email_verified_of_email_uid {w : PrivInputs Sig} {c : Claims}
    (h : R3EmailVerified w c) (hemail : w.uidKey = .email) :
    c.emailVerified = some (.jsonBool true) ∨ c.emailVerified = some (.quoted true) := by
  obtain ⟨ev, hev, hverified⟩ := h hemail
  cases ev with
  | jsonBool b => cases b <;> simp_all [EvValue.isVerified]
  | quoted b   => cases b <;> simp_all [EvValue.isVerified]

theorem evValue_matches_circuit (ev : EvValue) :
    ev.isVerified = true ↔ (ev.byteLen = 4 ∨ ev.byteLen = 6) := by
  cases ev with
  | jsonBool b => cases b <;> simp [EvValue.isVerified, EvValue.byteLen]
  | quoted b   => cases b <;> simp [EvValue.isVerified, EvValue.byteLen]

/-- When `uid_key ≠ "email"` the circuit constrains nothing about `email_verified`. Sound today
only because no `ev_*` signal reaches the identity commitment. -/
theorem ev_unconstrained_when_not_email {w : PrivInputs Sig} {c : Claims}
    (hne : w.uidKey ≠ .email) (ev : Option EvValue) :
    R3EmailVerified w { c with emailVerified := ev } := by
  intro hemail
  exact absurd hemail hne

theorem expDate_lt_iat_add_horizon {p : PubInputs Epk Jwk Commit} {c : Claims}
    (h : R8ExpDateBounded p c) : p.expDate < c.iat + p.expHorizon :=
  h

end Lemmas

/-! ## Obligations discharged outside the relation

Hypotheses from AIP-61 (outside the circuit). -/

/-- `iss_val` names the provider whose key signed the token. Nothing in the relation ties the two together directly. -/
def IssuerKeyBound (issVal keyOwner : String) : Prop :=
  issVal = keyOwner

/-- "Assert `exp_horizon ∈ (0, max_exp_horizon)`", an on-chain parameter check. -/
def ExpHorizonBounded (expHorizon maxExpHorizon : Nat) : Prop :=
  0 < expHorizon ∧ expHorizon < maxExpHorizon

/-- "Assert `current_block_time() < exp_date`". The relation deliberately does not check the EPK is unexpired. -/
def EpkNotExpired (currentTime expDate : Nat) : Prop :=
  currentTime < expDate

/-- The recovery-service `aud` is on the on-chain override list. Only meaningful in `AudMode.override` mode; irrelevant in `normal`/`skipped` mode. -/
def OverrideAudAllowlisted (ovr : String) (allowed : List String) : Prop :=
  ovr ∈ allowed

/-!
Note on `AudMode.skipped`: since `R5`/`R6` assert nothing about any `aud` value in this mode, an
aud-less identity is not bound to any consistent `aud` at all.
-/

end Spec.KeylessSpec

/-! ## some tests -/

namespace TestKeylessSpec

open Spec.KeylessSpec

/-! ### email_verified encoding table -/

example : (EvValue.jsonBool true).isVerified = true := by native_decide
example : (EvValue.quoted true).isVerified = true := by native_decide
example : (EvValue.jsonBool false).isVerified = false := by native_decide
example : (EvValue.quoted false).isVerified = false := by native_decide

example : (EvValue.jsonBool true).byteLen = 4 := by native_decide
example : (EvValue.quoted true).byteLen = 6 := by native_decide
example : (EvValue.jsonBool false).byteLen = 5 := by native_decide
example : (EvValue.quoted false).byteLen = 7 := by native_decide

example : EvValue.jsonBool true ≠ EvValue.quoted true := by native_decide

example : UidKey.sub.fieldName = "sub" := rfl
example : UidKey.email.fieldName = "email" := rfl

/-- A representative `Claims`. -/
def sample : Claims :=
  { iss           := "https://accounts.google.com"
    aud           := some "client-id"
    uidVal        := "1320606"
    nonce         := 12345678901234567890
    iat           := 1700000000
    emailVerified := some (.jsonBool true) }

example : sample.aud = some "client-id" := rfl

/-- `normal` mode: the JWT's `aud` must equal the prover's real `aud_val`. -/
example :
    R6AudMatches (Epk := Unit) (Jwk := Unit) (Commit := Unit) (Sig := Unit)
      { epk := (), addrIdc := (), expDate := 0, expHorizon := 0, issVal := ""
        extraField := none, header := "", jwk := (), audMode := .normal }
      { audVal := "client-id", uidKey := .sub, uidVal := "1320606", pepper := 0
        sigOidc := (), jwt := "", epkBlinder := 0 }
      sample := rfl

/-- `override` (recovery) mode: the JWT's `aud` must equal the override, regardless of the
prover's real `aud_val`. -/
example :
    R6AudMatches (Epk := Unit) (Jwk := Unit) (Commit := Unit) (Sig := Unit)
      { epk := (), addrIdc := (), expDate := 0, expHorizon := 0, issVal := ""
        extraField := none, header := "", jwk := (), audMode := .override "recovery-service" }
      { audVal := "client-id", uidKey := .sub, uidVal := "1320606", pepper := 0
        sigOidc := (), jwt := "", epkBlinder := 0 }
      { sample with aud := some "recovery-service" } := rfl

/-- `skipped` mode: holds no matter what `c.aud` is, including absent. -/
example :
    R6AudMatches (Epk := Unit) (Jwk := Unit) (Commit := Unit) (Sig := Unit)
      { epk := (), addrIdc := (), expDate := 0, expHorizon := 0, issVal := ""
        extraField := none, header := "", jwk := (), audMode := .skipped }
      { audVal := "client-id", uidKey := .sub, uidVal := "1320606", pepper := 0
        sigOidc := (), jwt := "", epkBlinder := 0 }
      { sample with aud := none } := trivial

/-- Conjunct 9 is satisfied whenever the abstract `TopLevelSubstring` predicate holds of the raw
bytes against the raw JWT string -/
example {TopLevelSubstring : String → String → Prop}
    (h : TopLevelSubstring "the raw jwt payload" "\"amr\":[\"pwd\",\"mfa\"]") :
    R9ExtraFieldMatches (Epk := Unit) (Jwk := Unit) (Commit := Unit) (Sig := Unit)
      TopLevelSubstring
      { epk := (), addrIdc := (), expDate := 0, expHorizon := 0, issVal := ""
        extraField := some "\"amr\":[\"pwd\",\"mfa\"]", header := "", jwk := (), audMode := .normal }
      { audVal := "client-id", uidKey := .sub, uidVal := "1320606", pepper := 0
        sigOidc := (), jwt := "the raw jwt payload", epkBlinder := 0 } := by
  simpa [R9ExtraFieldMatches] using h

/-- An absent extra field is vacuous, regardless of `TopLevelSubstring`. -/
example {TopLevelSubstring : String → String → Prop} :
    R9ExtraFieldMatches (Epk := Unit) (Jwk := Unit) (Commit := Unit) (Sig := Unit)
      TopLevelSubstring
      { epk := (), addrIdc := (), expDate := 0, expHorizon := 0, issVal := ""
        extraField := none, header := "", jwk := (), audMode := .normal }
      { audVal := "client-id", uidKey := .sub, uidVal := "1320606", pepper := 0
        sigOidc := (), jwt := "anything", epkBlinder := 0 } :=
  trivial

/-- Conjunct 3 is vacuous for a `sub`-keyed identity. -/
example :
    R3EmailVerified (Sig := Unit)
      { audVal := "client-id", uidKey := .sub, uidVal := "1320606", pepper := 0
        sigOidc := (), jwt := "", epkBlinder := 0 }
      { sample with emailVerified := none } := by
  simp [R3EmailVerified]

/-- ...and non-vacuous for an `email`-keyed one: an absent `email_verified` is rejected. -/
example :
    ¬ R3EmailVerified (Sig := Unit)
        { audVal := "client-id", uidKey := .email, uidVal := "a@b.com", pepper := 0
          sigOidc := (), jwt := "", epkBlinder := 0 }
        { sample with uidVal := "a@b.com", emailVerified := none } := by
  simp [R3EmailVerified]

/-- The email witness, for the encoding cases below. -/
def emailWitness : PrivInputs Unit :=
  { audVal := "client-id", uidKey := .email, uidVal := "a@b.com", pepper := 0
    sigOidc := (), jwt := "", epkBlinder := 0 }

/-- An unquoted `true` passes. -/
example :
    R3EmailVerified emailWitness
      { sample with uidVal := "a@b.com", emailVerified := some (.jsonBool true) } := by
  simp [R3EmailVerified, emailWitness, EvValue.isVerified]

/-- A quoted `"true"` passes too. -/
example :
    R3EmailVerified emailWitness
      { sample with uidVal := "a@b.com", emailVerified := some (.quoted true) } := by
  simp [R3EmailVerified, emailWitness, EvValue.isVerified]

/-- An unquoted `false` fails. -/
example :
    ¬ R3EmailVerified emailWitness
        { sample with uidVal := "a@b.com", emailVerified := some (.jsonBool false) } := by
  simp [R3EmailVerified, emailWitness, EvValue.isVerified]

/-- ...and so does a quoted `"false"`. -/
example :
    ¬ R3EmailVerified emailWitness
        { sample with uidVal := "a@b.com", emailVerified := some (.quoted false) } := by
  simp [R3EmailVerified, emailWitness, EvValue.isVerified]

end TestKeylessSpec
