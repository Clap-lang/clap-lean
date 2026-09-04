import Clap.Lang
import Clap.JWT
import Clap.KeylessJSON

/-!
Draft spec relating `JWT.lean`'s field-parsing circuit gadgets
(`JWT.parseJWTFieldWithUnquotedValue`, `JWT.parseJWTFieldWithQuotedValue`) to
`KeylessJSON.lean`'s independent reference JSON parser
(`Keyless.payloads_from_json_string`).

Goal: if the reference parser accepts a payload string and extracts a given field value,
then there exist circuit-witness parameters under which the corresponding circuit gadget
returns `some ()`.

This is a **statement-only draft** (`sorry`-terminated) meant to check that this shape of
lemma is the right one, before attempting real proofs.

The `exists_..._of_parses_...` theorems below only require `fi.field`/`fi.nameIndex`/
`fi.colonIndex`/`fi.valueIndex` to make the gadget accept *some* self-consistent witness; they
do not require `fi.field` to actually occur inside `payload` at `fi.nameIndex`. The
`exists_..._of_parses..._located` theorems strengthen this by adding exactly that requirement,
so the two accepted circuit witnesses can be compared side by side. Long-term this located
condition should probably be stated using the `Spec.FString`/`FString.isSubstringFS` machinery
that `JWT.parseJWTFieldSharedLogic` itself is built on (`Clap/FString.lean:191-230`); for now it
is stated directly at the plain-`String`/`List Char` level.
-/

open Clap.Lang

set_option warn.sorry false in
/-- If the reference JSON parser accepts `payload` as a JWT-payload-shaped JSON object and
extracts a payload `p` from it, there exist circuit-witness parameters under which
`JWT.parseJWTFieldWithUnquotedValue` accepts the `iat` field with `p`'s value. -/
theorem exists_unquotedFieldInput_of_parses_iat
    (uidKey : Keyless.UidKey) (extraFieldKey payload : String)
    (payloads : List Keyless.AptosPayload)
    (h : Keyless.payloads_from_json_string uidKey extraFieldKey payload = Except.ok payloads)
    (p : Keyless.AptosPayload) (hp : p ∈ payloads) :
    ∃ (maxKVPairLen maxNameLen maxValueLen : ℕ)
      (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
      (fi : JWT.UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen),
      Spec.FString.toString fi.name = "iat" ∧
      Spec.FString.toString fi.value = toString p.iat ∧
      JWT.parseJWTFieldWithUnquotedValue fi h_name h_value = some () := by
  sorry

set_option warn.sorry false in
/-- Same statement for the quoted `aud` field against `JWT.parseJWTFieldWithQuotedValue`. -/
theorem exists_quotedFieldInput_of_parses_aud
    (uidKey : Keyless.UidKey) (extraFieldKey payload : String)
    (payloads : List Keyless.AptosPayload)
    (h : Keyless.payloads_from_json_string uidKey extraFieldKey payload = Except.ok payloads)
    (p : Keyless.AptosPayload) (hp : p ∈ payloads) :
    ∃ (maxKVPairLen maxNameLen maxValueLen : ℕ)
      (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
      (fi : JWT.QuotedFieldInput maxKVPairLen maxNameLen maxValueLen),
      Spec.FString.toString fi.name = "aud" ∧
      Spec.FString.toString fi.value = p.aud ∧
      JWT.parseJWTFieldWithQuotedValue fi h_name h_value = some () := by
  sorry

set_option warn.sorry false in
/-- Strengthens `exists_unquotedFieldInput_of_parses_iat`: the witness `fi.field` is
additionally required to be the actual slice of `payload` at `fi.nameIndex`, not just an
arbitrary self-consistent string. -/
theorem exists_unquotedFieldInput_of_parses_iat_located
    (uidKey : Keyless.UidKey) (extraFieldKey payload : String)
    (payloads : List Keyless.AptosPayload)
    (h : Keyless.payloads_from_json_string uidKey extraFieldKey payload = Except.ok payloads)
    (p : Keyless.AptosPayload) (hp : p ∈ payloads) :
    ∃ (maxKVPairLen maxNameLen maxValueLen : ℕ)
      (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
      (fi : JWT.UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen),
      Spec.FString.toString fi.name = "iat" ∧
      Spec.FString.toString fi.value = toString p.iat ∧
      (payload.toList.drop fi.nameIndex.val).take fi.field.len.val
        = (Spec.FString.toString fi.field).toList ∧
      JWT.parseJWTFieldWithUnquotedValue fi h_name h_value = some () := by
      -- TODO: refine, make sure
  sorry

set_option warn.sorry false in
/-- Strengthens `exists_quotedFieldInput_of_parses_aud` the same way. -/
theorem exists_quotedFieldInput_of_parses_aud_located
    (uidKey : Keyless.UidKey) (extraFieldKey payload : String)
    (payloads : List Keyless.AptosPayload)
    (h : Keyless.payloads_from_json_string uidKey extraFieldKey payload = Except.ok payloads)
    (p : Keyless.AptosPayload) (hp : p ∈ payloads) :
    ∃ (maxKVPairLen maxNameLen maxValueLen : ℕ)
      (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
      (fi : JWT.QuotedFieldInput maxKVPairLen maxNameLen maxValueLen),
      Spec.FString.toString fi.name = "aud" ∧
      Spec.FString.toString fi.value = p.aud ∧
      (payload.toList.drop fi.nameIndex.val).take fi.field.len.val
        = (Spec.FString.toString fi.field).toList ∧
      JWT.parseJWTFieldWithQuotedValue fi h_name h_value = some () := by
  sorry
