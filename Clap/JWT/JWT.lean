import Clap.JWT.Json
import Mathlib.Algebra.Field.Rat

/-!
# A specification of JSON Web Tokens

This file specifies JWT, building on `Clap/JWT/Json.lean`'s RFC 8259 JSON model. It
follows the standards stack rather than any implementation, one namespace per layer:

| namespace         | standard                  | contents                                        |
|-------------------|---------------------------|-------------------------------------------------|
| `Spec.Base64Url`  | RFC 4648 §5               | unpadded base64url encoding                     |
| `Spec.Jws`        | RFC 7515                  | the JWS compact serialization                   |
| `Spec.JwtClaims`  | RFC 7519                  | Claims Set, registered claims, `NumericDate`    |
| `Spec.Oidc`       | OpenID Connect Core 1.0   | the `nonce`/`email`/`email_verified` claims     |

RFC 7515 requires a JWS header to be a JSON object but places no structure requirement on the payload,
a JWS carries arbitrary content. RFC 7519's specific contribution is that for a JWT the payload happens
to be a UTF-8 JSON Claims Set, so that is isolated in `IsJwt` rather than baked into the `Jws` structure.

Specification only
-/

/-! ## `Spec.Base64Url` (RFC 4648 §5 base64url encoding) -/

namespace Spec.Base64Url

/-- RFC 4648 §5 base64url encoding, unpadded -/
def encode : List UInt8 → String := by sorry

/-- RFC 4648 §5's alphabet, checked character-by-character. Note `=` is excluded: it is a padding
character, and RFC 7515 §2 requires padding to be omitted entirely. -/
def IsBase64UrlChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_'

def IsBase64UrlAlphabet (s : String) : Prop := ∀ c ∈ s.toList, IsBase64UrlChar c

/-- base64url spec `s` is exactly the encoding of `bytes`. -/
def Encodes (bytes : List UInt8) (s : String) : Prop := s = encode bytes

def IsBase64Url (s : String) : Prop := ∃ bytes, Encodes bytes s

theorem encode_isBase64UrlAlphabet (bytes : List UInt8) :
    IsBase64UrlAlphabet (encode bytes) := by
  sorry

/-- `encode` is injective -/
theorem Encodes.unique {bytes₁ bytes₂ : List UInt8} {s : String} :
    Encodes bytes₁ s → Encodes bytes₂ s → bytes₁ = bytes₂ := by
  sorry

/-- `.` is not in the base64url alphabet. This is what makes the two `.` separators of a compact
serialization unambiguous, and hence what `Spec.Jws.Reconstructs.unique` rests on. -/
theorem dot_not_isBase64UrlChar : ¬ IsBase64UrlChar '.' := by decide

end Spec.Base64Url

/-! ## `Spec.Jws` (RFC 7515 (JWS compact serialization)) -/

namespace Spec

open Spec.Json Spec.Base64Url

/-- RFC 7515 §3.1's JWS Compact Serialization. base64url segments, carrying the
decoded header document + payload bytes + and signature bytes alongside their encoded text.

The payload is raw bytes, not a `Doc`: RFC 7515 imposes no structure on a JWS payload — that is
RFC 7519's addition, and it lives in `Spec.JwtClaims.IsJwt`.

RFC 7515 also defines a JSON Serialization (§7, supporting multiple signatures); it is not modelled here. -/
structure Jws where
  headerSeg    : String
  payloadSeg   : String
  signatureSeg : String
  headerDoc    : Doc
  payload      : List UInt8
  signature    : List UInt8
deriving Repr

namespace Jws

def serialize (j : Jws) : String := j.headerSeg ++ "." ++ j.payloadSeg ++ "." ++ j.signatureSeg

/-- `s` is exactly `j`'s three joined segments; the JOSE Header is a JSON object (RFC 7515 §4); and
each segment is exactly the base64url encoding of its decoded content, the header via its UTF-8
bytes (RFC 7515 §3.1's `BASE64URL(UTF8(JWS Protected Header))`).

Nothing is asserted about the payload's shape, and no header parameter is required: in
particular RFC 7515 §4.1.1's "`alg` MUST be present" is not modelled, only the object-ness of
the header. -/
def Reconstructs (s : String) (j : Jws) : Prop :=
  s = serialize j ∧
  IsObjectDoc j.headerDoc ∧
  Encodes (Doc.serialize j.headerDoc).toUTF8.data.toList j.headerSeg ∧
  Encodes j.payload j.payloadSeg ∧
  Encodes j.signature j.signatureSeg

theorem reconstructs_serialize {j : Jws} (hh : IsObjectDoc j.headerDoc) :
    Reconstructs (serialize j) j := by
  sorry

/-- Uniqueness of `Jws` rests on three facts: the split of `s` at its two `.`
separators is unique (`dot_not_isBase64UrlChar`), `Encodes.unique` for each segment, and the
injectivity of `String.toUTF8` for the header. -/
theorem Reconstructs.unique {s : String} {j₁ j₂ : Jws} :
    Reconstructs s j₁ → Reconstructs s j₂ → j₁ = j₂ := by
  sorry

end Jws

end Spec

/-! ## `Spec.JwtClaims` (RFC 7519) -/

namespace Spec.JwtClaims

open Spec.Json Spec.Base64Url Spec.Jws

/-- RFC 7519 §7.2: a JWT Claims Set MUST be a JSON object -/
def IsClaimSet (d : Doc) : Prop := IsObjectDoc d

/-- a `Jws` is a JWT exactly when its payload is the UTF-8 encoding of a JSON Claims Set (§7.2 steps 9-10).

Everything JWT-specific below is stated against the witness `Doc`, not against `Jws`, so the claim
vocabulary stays decoupled from the base64/serialization machinery

RFC 7519 §3 also permits a JWT to be a JWE (five segments, encrypted, no `Jws` shape at
all), §5.2 permits nested JWTs (`cty: "JWT"`, whose payload is another JWT rather than a JSON
object), and §6 defines Unsecured JWTs (`alg: "none"`). None are modelled. We only model the "ordinary"
signed-JWT-over-JWS-compact-serialization case. -/
def IsJwt (j : Jws) : Prop :=
  ∃ d : Doc, IsClaimSet d ∧ j.payload = (Doc.serialize d).toUTF8.data.toList

/-- The Claims Set of a JWT is unique -/
theorem IsJwt.doc_unique {j : Jws} {d₁ d₂ : Doc}
    (h₁ : IsClaimSet d₁ ∧ j.payload = (Doc.serialize d₁).toUTF8.data.toList)
    (h₂ : IsClaimSet d₂ ∧ j.payload = (Doc.serialize d₂).toUTF8.data.toList) :
    d₁ = d₂ := by
  sorry

/-- Top-level, string-facing predicate: `s` is text that reconstructs as a JWT. -/
def IsJwtString (s : String) : Prop := ∃ j, Reconstructs s j ∧ IsJwt j

/-! ### Claim value types (RFC 7519 §2) -/

/-- RFC 3986 URI syntax -/
def IsUri (_s : String) : Prop := True

/-- RFC 7519 §2's `StringOrURI`: "A JSON string value, with the additional requirement that while
arbitrary string values MAY be used, any value containing a `:` character MUST be a URI."

The `:`-conditional is the whole content of the type; without it this would be a renaming of
`IsStrBody`, which every string-valued member satisfies anyway (`hasMember_isStrBody`). -/
def StringOrURI (s : String) : Prop :=
  IsStrBody s ∧ (':' ∈ s.toList → IsUri s)

/-- Decimal value of a digit list, most-significant digit first -/
def digitsVal (ds : List Char) : ℕ := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Value of a number literal's fractional part (`Spec.Json.IsFracPart`'s grammar: `[]` or
`'.' :: ds`). -/
def fracVal : List Char → ℚ
  | '.' :: ds => (digitsVal ds : ℚ) / (10 : ℚ) ^ ds.length
  | _ => 0

/-- Value of a number literal's exponent part (`Spec.Json.IsExpPart`'s grammar: `[]` or
`(e|E) :: (sign? ++ digits)`) -/
def expVal : List Char → ℤ
  | [] => 0
  | _ :: '-' :: ds => -(digitsVal ds : ℤ)
  | _ :: '+' :: ds => (digitsVal ds : ℤ)
  | _ :: ds => (digitsVal ds : ℤ)

/-- RFC 7519 §2's `NumericDate`: "a JSON numeric value representing the number of seconds from
1970-01-01T00:00:00Z UTC until the specified UTC date/time, ignoring leap seconds" -/
def NumericDateDecodes (lit : String) (q : ℚ) : Prop := True

/-- A literal that decodes is a literal of the grammar -/
theorem numericDateDecodes_isNumLit {lit : String} {q : ℚ} :
    NumericDateDecodes lit q → IsNumLit lit := by
  sorry

theorem NumericDateDecodes.unique {lit : String} {q₁ q₂ : ℚ} :
    NumericDateDecodes lit q₁ → NumericDateDecodes lit q₂ → q₁ = q₂ := by
  sorry

/-! ### Registered claim names (RFC 7519 §4.1)

Stated against a bare `Doc` (the Claims Set) using `Spec.Json.HasMember`. Note that is the
non-unique reading: a Claims Set carrying two `"iss"` members satisfies `HasIss` for both values.
RFC 7519 inherits RFC 8259's silence on duplicate names -/

/-- §4.1.1 `iss`: "identifies the principal that issued the JWT". -/
def HasIss (d : Doc) (iss : String) : Prop := HasMember d.val "iss" (.str iss)

/-- §4.1.2 `sub`: "identifies the principal that is the subject of the JWT". -/
def HasSub (d : Doc) (sub : String) : Prop := HasMember d.val "sub" (.str sub)

/-- §4.1.7 `jti`: a unique identifier for the JWT. A plain string — unlike `iss`/`sub`/`aud` the
RFC does not type it as `StringOrURI`. -/
def HasJti (d : Doc) (jti : String) : Prop := HasMember d.val "jti" (.str jti)

/-- §4.1.3 `aud`: "a case-sensitive string containing a `StringOrURI` value ... or ... an array of
case-sensitive strings" -/
def HasAud (d : Doc) (auds : List String) : Prop :=
  (∃ v, auds = [v] ∧ HasMember d.val "aud" (.str v)) ∨
  (∃ ws es, HasMember d.val "aud" (.arr ws es) ∧
     List.Forall₂ (fun (e : Elem Value) (s : String) => e.val = .str s) es auds)

/-- The recipient's question, per §4.1.3: "the principal processing the claim MUST identify itself
with a value in the audience claim". RFC 7519 does not forbid an empty `aud` array. -/
def HasAudMember (d : Doc) (aud : String) : Prop := ∃ auds, HasAud d auds ∧ aud ∈ auds

/-- §4.1.4 `exp`: the expiration time on or after which the JWT must not be accepted. -/
def HasExp (d : Doc) (q : ℚ) : Prop :=
  ∃ lit, HasMember d.val "exp" (.num lit) ∧ NumericDateDecodes lit q

/-- §4.1.5 `nbf`: the time before which the JWT must not be accepted. -/
def HasNbf (d : Doc) (q : ℚ) : Prop :=
  ∃ lit, HasMember d.val "nbf" (.num lit) ∧ NumericDateDecodes lit q

/-- §4.1.6 `iat`: the time at which the JWT was issued. -/
def HasIat (d : Doc) (q : ℚ) : Prop :=
  ∃ lit, HasMember d.val "iat" (.num lit) ∧ NumericDateDecodes lit q

/-! ### Temporal validity (RFC 7519 §4.1.4, §4.1.5)

`exp` and `nbf` are the only registered claims with normative processing rules. Both claims are
OPTIONAL, which is why each is stated as a `∀` over the decoded value. A
Claims Set carrying no `exp` is vacuously unexpired, exactly as the RFC intends. -/

/-- §4.1.4: "the current date/time MUST be before the expiration date/time listed in the `exp`
claim". -/
def NotExpiredAt (d : Doc) (now : ℚ) : Prop := ∀ q, HasExp d q → now < q

/-- §4.1.5: "the current date/time MUST be after or equal to the not-before date/time listed in the
`nbf` claim". -/
def NotBeforeOk (d : Doc) (now : ℚ) : Prop := ∀ q, HasNbf d q → q ≤ now

/-- The temporal half of RFC 7519 §7.2 validation, at time `now`. -/
def IsActiveAt (d : Doc) (now : ℚ) : Prop := NotExpiredAt d now ∧ NotBeforeOk d now

/-! ### Claim values are well formed -/

/-- Any string-valued member of a well-formed document has a legal string body -/
theorem hasMember_isStrBody {d : Doc} {name value : String}
    (hd : DocWF d) (h : HasMember d.val name (.str value)) : IsStrBody value := by
  sorry

/-- §4.1.1 types `iss` as `StringOrURI`. -/
theorem hasIss_stringOrURI {d : Doc} {iss : String}
    (hd : DocWF d) (h : HasIss d iss) : StringOrURI iss := by
  sorry

/-- §4.1.2 types `sub` as `StringOrURI`. -/
theorem hasSub_stringOrURI {d : Doc} {sub : String}
    (hd : DocWF d) (h : HasSub d sub) : StringOrURI sub := by
  sorry

/-- §4.1.3 types every audience. -/
theorem hasAud_stringOrURI {d : Doc} {auds : List String} {aud : String}
    (hd : DocWF d) (h : HasAud d auds) (hmem : aud ∈ auds) : StringOrURI aud := by
  sorry

/-! ### Public and private claim names (RFC 7519 §4.2, §4.3)

Any name beyond the registered set may carry a claim. Deliberately permissive: §4.2's
collision-resistance and §4.3's "by mutual agreement" are naming conventions -/

def HasClaim (d : Doc) (name : String) (v : Value) : Prop := HasMember d.val name v
def HasStringClaim (d : Doc) (name value : String) : Prop := HasMember d.val name (.str value)

end Spec.JwtClaims

/-! ## `Spec.Oidc` — OpenID Connect Core 1.0

Claims defined by OpenID Connect rather than RFC 7519 itself, kept in their own namespace so the
RFC 7519 layer above stays exactly RFC 7519. These are the ones an ID Token carries in practice.
-/

namespace Spec.Oidc

open Spec.Json Spec.JwtClaims

/-- OIDC Core 1.0 §2: the `nonce` an ID Token echoes back from the authentication request, used "to
associate a Client session with an ID Token, and to mitigate replay attacks". Its value is an
opaque string as far as the standard is concerned -/
def HasNonce (d : Doc) (nonce : String) : Prop := HasStringClaim d "nonce" nonce

/-- OIDC Core 1.0 §5.1: the End-User's preferred e-mail address. The standard warns this value is
not guaranteed unique or stable, so it is a string here with no format validation. -/
def HasEmail (d : Doc) (email : String) : Prop := HasStringClaim d "email" email

/-- `email_verified` as OIDC Core 1.0 §5.1 specifies it as JSON `boolean`. -/
def HasEmailVerifiedBool (d : Doc) (b : Bool) : Prop := HasMember d.val "email_verified" (.bool b)

/-- `email_verified` as some providers actually emit it as quoted `"true"`/`"false"` string -/
def HasEmailVerifiedString (d : Doc) (b : Bool) : Prop :=
  HasMember d.val "email_verified" (.str (if b then "true" else "false"))

/-- "The e-mail address is verified", accepting either encoding. A relying party that checks only
the boolean form silently fails open against providers using the string form, which is why the
disjunction is stated -/
def EmailVerifiedTrue (d : Doc) : Prop :=
  HasEmailVerifiedBool d true ∨ HasEmailVerifiedString d true

end Spec.Oidc

/-! ## Validation -/

namespace TestJwtClaims

open Spec Spec.Json Spec.Base64Url Spec.Jws Spec.JwtClaims Spec.Oidc

/-! ### Base64url: the three tail cases (0/1/2 leftover bytes) -/

-- example : encode "Man".toUTF8.data.toList = "TWFu" := by native_decide
-- example : encode "Ma".toUTF8.data.toList = "TWE" := by native_decide
-- example : encode "M".toUTF8.data.toList = "TQ" := by native_decide

/-! ### A representative ID Token Claims Set -/

/-- Registered claims (`iss`/`aud`/`sub`/`iat`/`exp`) alongside OIDC ones (`email`,
`email_verified` in its quoted-string form, `nonce`) and a private claim (`name`). -/
def sample : Doc :=
  ⟨"", .obj "" [
    ⟨"",  "iss",            "", ⟨" ", .str "https://accounts.google.com", ""⟩⟩,
    ⟨" ", "aud",            "", ⟨" ", .str "my-client-id", ""⟩⟩,
    ⟨" ", "sub",            "", ⟨" ", .str "10769150350006150715113082367", ""⟩⟩,
    ⟨" ", "email",          "", ⟨" ", .str "alice@example.com", ""⟩⟩,
    ⟨" ", "email_verified", "", ⟨" ", .str "true", ""⟩⟩,
    ⟨" ", "iat",            "", ⟨" ", .num "1700000000", ""⟩⟩,
    ⟨" ", "exp",            "", ⟨" ", .num "1700003600", ""⟩⟩,
    ⟨" ", "nonce",          "", ⟨" ", .str "abc123nonce", ""⟩⟩,
    ⟨" ", "name",           "", ⟨" ", .str "Alice Example", ""⟩⟩],
   ""⟩

/-- Sibling of `sample` with `email_verified` in the standard bare-boolean form. -/
def sampleBoolEV : Doc :=
  ⟨"", .obj "" [
    ⟨"",  "iss",            "", ⟨" ", .str "https://accounts.google.com", ""⟩⟩,
    ⟨" ", "email",          "", ⟨" ", .str "alice@example.com", ""⟩⟩,
    ⟨" ", "email_verified", "", ⟨" ", .bool true, ""⟩⟩],
   ""⟩

/-- Sibling of `sample` with `aud` in its array form, per RFC 7519 §4.1.3. -/
def sampleAudArray : Doc :=
  ⟨"", .obj "" [
    ⟨"", "aud", "", ⟨" ", .arr "" [⟨"", .str "client-a", ""⟩, ⟨" ", .str "client-b", ""⟩], ""⟩⟩],
   ""⟩

example : HasIss sample "https://accounts.google.com" := by
  refine ⟨_, rfl, ?_⟩; simp

example : HasSub sample "10769150350006150715113082367" := by
  refine ⟨_, rfl, ?_⟩; simp

example : HasEmail sample "alice@example.com" := by
  refine ⟨_, rfl, ?_⟩; simp

example : HasNonce sample "abc123nonce" := by
  refine ⟨_, rfl, ?_⟩; simp

/-- A private claim (§4.3), reached through the generic accessor. -/
example : HasClaim sample "name" (.str "Alice Example") := by
  refine ⟨_, rfl, ?_⟩; simp

/-- `aud` as a bare string is the singleton case of the union. -/
example : HasAud sample ["my-client-id"] := by
  left
  refine ⟨_, rfl, _, rfl, ?_⟩; simp

example : HasAudMember sample "my-client-id" := ⟨["my-client-id"], by
  left
  refine ⟨_, rfl, _, rfl, ?_⟩; simp, by simp⟩

/-- `aud` as an array is the other case, related pointwise by `List.Forall₂`. -/
example : HasAud sampleAudArray ["client-a", "client-b"] := by
  right
  refine ⟨"", [⟨"", .str "client-a", ""⟩, ⟨" ", .str "client-b", ""⟩], ?_, ?_⟩
  · refine ⟨_, rfl, ?_⟩; simp
  · exact List.Forall₂.cons rfl (List.Forall₂.cons rfl List.Forall₂.nil)

/-- Both `aud` encodings answer the recipient's question the same way — the point of surfacing the
union as a `List String`. -/
example : HasAudMember sampleAudArray "client-b" :=
  ⟨["client-a", "client-b"],
    by right
       refine ⟨"", [⟨"", .str "client-a", ""⟩, ⟨" ", .str "client-b", ""⟩], ?_, ?_⟩
       · refine ⟨_, rfl, ?_⟩; simp
       · exact List.Forall₂.cons rfl (List.Forall₂.cons rfl List.Forall₂.nil),
    by simp⟩

/-- The non-standard quoted form of `email_verified`. -/
example : EmailVerifiedTrue sample := by
  right
  refine ⟨_, rfl, ?_⟩; simp

/-- The standard boolean form. Both satisfy `EmailVerifiedTrue`; a check written against only one
would not. -/
example : EmailVerifiedTrue sampleBoolEV := by
  left
  refine ⟨_, rfl, ?_⟩; simp

/-! ### `NumericDate` decoding, and the temporal rules -/

-- example : NumericDateDecodes "1700000000" (1700000000 : ℚ) := by
--   refine ⟨[], "1700000000".toList, [], [], by decide, Or.inl rfl, ?_, Or.inl rfl, Or.inl rfl, ?_⟩
--   · right
--     refine ⟨'1', "700000000".toList, by decide, by decide, by decide, by decide⟩
--   · native_decide

-- example : HasIat sample (1700000000 : ℚ) := by
--   refine ⟨"1700000000", ⟨_, rfl, ?_⟩, ?_⟩
--   · simp
--   · refine ⟨[], "1700000000".toList, [], [], by decide, Or.inl rfl, ?_, Or.inl rfl, Or.inl rfl, ?_⟩
--     · right
--       refine ⟨'1', "700000000".toList, by decide, by decide, by decide, by decide⟩
--     · native_decide

/-- A Claims Set with no `nbf` is vacuously past its not-before time — the `∀`-form of the temporal
predicates at work, matching that the claim is OPTIONAL. -/
example : NotBeforeOk sampleAudArray 0 := by
  rintro q ⟨lit, ⟨ms, hms, m, hm, hk, _⟩, -⟩
  simp [sampleAudArray, Value.membs?] at hms
  subst hms
  simp at hm
  rcases hm with rfl
  simp_all

/-! ### `Jws`, `Reconstructs` and `IsJwt`, end to end

`IsObjectDoc`/`IsClaimSet` have no `Decidable` instance (`StrBodyChars` and `IsNumLit` are
existential rather than bounded-∀), so unlike the checks above these need hand-built witnesses.
`strBody_of_printable` supplies the bridge — `StrBodyChars`'s per-character side condition *is* a
decidable bounded-∀ — after which everything reduces to `decide`. Kept to a one-member header and
one-member Claims Set to keep the witnesses small. -/

private theorem strBody_of_printable (s : List Char)
    (h : ∀ c ∈ s, c ≠ '"' ∧ c ≠ '\\' ∧ 0x20 ≤ c.toNat) : StrBodyChars s := by
  induction s with
  | nil => exact .nil
  | cons c cs ih =>
    have hc := h c (by simp)
    exact .lit hc.1 hc.2.1 hc.2.2 (ih (fun c' hc' => h c' (by simp [hc'])))

/-- `IsWs`'s bounded-∀ is decidable once unfolded, but typeclass search will not see through the
`def` on its own — hence this, rather than a bare `by decide` at each empty whitespace slot. -/
private theorem isWs_empty : IsWs "" := by
  unfold Spec.Json.IsWs
  decide

/-- A minimal JOSE Header, `{"alg":"RS256"}`. -/
def headerDoc : Doc :=
  ⟨"", .obj "" [⟨"", "alg", "", ⟨"", .str "RS256", ""⟩⟩], ""⟩

theorem headerDoc_isObject : IsObjectDoc headerDoc := by
  refine ⟨?_, rfl⟩
  refine ElemWF.mk isWs_empty ?_ isWs_empty
  refine ValueWF.obj isWs_empty (fun _ => rfl) ?_
  refine MembsWF.cons ?_ MembsWF.nil
  refine MembWF.mk isWs_empty (strBody_of_printable _ (by decide)) isWs_empty ?_
  refine ElemWF.mk isWs_empty ?_ isWs_empty
  exact ValueWF.str (strBody_of_printable _ (by decide))

/-- A minimal Claims Set, `{"aud":"my-client-id"}`. -/
def minimalClaims : Doc :=
  ⟨"", .obj "" [⟨"", "aud", "", ⟨"", .str "my-client-id", ""⟩⟩], ""⟩

theorem minimalClaims_isClaimSet : IsClaimSet minimalClaims := by
  refine ⟨?_, rfl⟩
  refine ElemWF.mk isWs_empty ?_ isWs_empty
  refine ValueWF.obj isWs_empty (fun _ => rfl) ?_
  refine MembsWF.cons ?_ MembsWF.nil
  refine MembWF.mk isWs_empty (strBody_of_printable _ (by decide)) isWs_empty ?_
  refine ElemWF.mk isWs_empty ?_ isWs_empty
  exact ValueWF.str (strBody_of_printable _ (by decide))

/-- A signed JWT: header, Claims-Set payload, and an (arbitrary) signature. -/
def sampleJws : Jws :=
  { headerSeg    := encode (Doc.serialize headerDoc).toUTF8.data.toList
    payloadSeg   := encode (Doc.serialize minimalClaims).toUTF8.data.toList
    signatureSeg := encode [0, 1, 2, 3]
    headerDoc    := headerDoc
    payload      := (Doc.serialize minimalClaims).toUTF8.data.toList
    signature    := [0, 1, 2, 3] }

example : Reconstructs (Jws.serialize sampleJws) sampleJws :=
  ⟨rfl, headerDoc_isObject, rfl, rfl, rfl⟩

/-- ...and it really is a JWT, not merely a JWS: its payload is the serialization of a Claims Set. -/
example : IsJwt sampleJws := ⟨minimalClaims, minimalClaims_isClaimSet, rfl⟩

example : IsJwtString (Jws.serialize sampleJws) :=
  ⟨sampleJws, ⟨rfl, headerDoc_isObject, rfl, rfl, rfl⟩,
   minimalClaims, minimalClaims_isClaimSet, rfl⟩

end TestJwtClaims
