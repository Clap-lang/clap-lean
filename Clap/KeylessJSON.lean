import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

import Std.Internal.Parsec

import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.FString
import Clap.HashToField
import Clap.JWT
import Clap.Poseidon.Poseidon
import Clap.Base64Len
import Clap.Sha2.Keyless
import Clap.RSA
import Clap.Keyless

open Std.Internal.Parsec
open Std.Internal.Parsec.String

open Lean Json ToJson FromJson

namespace Keyless

#check Parser (List Json)

#check Lean.Json.parse

/-

A value of `StringOrURI` type that contains a ":" character must be a URI, not a string,
but for the Aptos case this is not important.

**iss**
  - of type `StringOrURI`, actually just a URI in the form of a quoted string

**aud**
  - of type `StringOrURI` (or array of `StringOrURI`s, but not for Aptos)

**uid_key** is The name of the key in the claim that maps to the user identifier; e.g., "sub" or "email"

**sub**
  - of type `StringOrURI`, actually just a string
  - It MUST NOT exceed 255 ASCII [RFC20] characters in length.

AIP-061 gives `email` as an example of `extra_field`

-/


/-

Public key:
  - *iss*
  - IDC (id commitment) = *uid* + ("sub" | "email") + *aud*

Signature verification against Public key:
  -

-/
inductive UidKey where
  | sub
  | email
  deriving BEq, Repr

/-- The name of the JSON field a `UidKey` refers to. -/
def UidKey.fieldName : UidKey → String
  | .sub   => "sub"
  | .email => "email"

structure AptosPayload where
  iss            : String
  -- The value of the field named by the request's uid key ("sub" or "email").
  uid            : String
  aud            : String
  iat            : ℕ
  -- exp            : ℕ
  email_verified : Bool
  nonce          : String
  -- The value of the field named by the request's extra field.
  extra_field    : String
  deriving Inhabited, Repr, BEq

/-- `email_verified` may be given as a JSON boolean (`true`/`false`) or as a JSON
string (`"true"`/`"false"`); any other value is rejected. -/
def emailVerifiedFromJson : Json → Except String Bool
  | .bool b     => return b
  | .str "true"  => return true
  | .str "false" => return false
  | .str s => throw s!"The field (email_verified) must be true, false, \"true\" or \"false\", but got (\"{s}\")."
  | _ => throw "The field (email_verified) must be a boolean or a string."

/-- A JSON value already dispatched, converted, and validated against one of
`AptosPayload`'s known fields (by `aptosFieldValueFromJson`). -/
inductive AptosFieldValue where
  | iss (s : String)
  | aud (s : String)
  | uid (s : String)
  | iat (n : ℕ)
  | emailVerified (b : Bool)
  | nonce (s : String)
  | extraField (s : String)
  deriving Repr, BEq

/-- Given a JSON key `key` and its already-parsed value `j`, checks which (if any) of
`AptosPayload`'s fields `key` names — given the per-request `uidKey`/`extraFieldKey`
configuration — and converts+validates `j` into the correspondingly typed
`AptosFieldValue`(s). This is what used to be `payload_from_json`'s per-field type checks
(`getObjValAs?`) and per-field semantic checks (the `nonce`/`email_verified` shape
checks), now applied right where each field's value is parsed instead of after the whole
JSON object has been assembled. `Json.getStr?`/`Json.getNat?` are the same conversions
`FromJson String`/`FromJson Nat` (hence `getObjValAs?`) use, so type-check behavior is
unchanged. The one remaining cross-field check (`uidKey == .email → email_verified`)
still needs the whole record, so it happens once per candidate in `AptosFieldAcc.toPayloads`.

`key` may name more than one field at once (e.g. `extraFieldKey == uidKey.fieldName`), in
which case `j` is converted for every field it names; if any of those conversions fails,
the whole call fails (matching what independently calling `getObjValAs?` once per field
against the same JSON value would do today). A `key` naming none of `AptosPayload`'s
fields yields `[]`. -/
def aptosFieldValueFromJson (uidKey : UidKey) (extraFieldKey key : String) (j : Json) :
    Except String (List AptosFieldValue) :=
  let roles : List (Option (Except String AptosFieldValue)) :=
    [ if key == "iss" then some (AptosFieldValue.iss <$> j.getStr?) else none
    , if key == "aud" then some (AptosFieldValue.aud <$> j.getStr?) else none
    , if key == uidKey.fieldName then some (AptosFieldValue.uid <$> j.getStr?) else none
    , if key == "iat" then some (AptosFieldValue.iat <$> j.getNat?) else none
    , if key == "email_verified" then
        some (AptosFieldValue.emailVerified <$> emailVerifiedFromJson j)
      else none
    , if key == "nonce" then
        some do
          let s ← j.getStr?
          if s.isEmpty || !s.all Char.isDigit then
            throw s!"The field (nonce) must be a non-empty digit string, but got (\"{s}\")."
          pure (AptosFieldValue.nonce s)
      else none
    , if key == extraFieldKey then some (AptosFieldValue.extraField <$> j.getStr?) else none
    ]
  roles.reduceOption.mapM id


/-- Accumulates one candidate list of typed values per `AptosPayload` field while
scanning a JSON object's key-value pairs, so a field appearing more than once (a
duplicate JSON key) still yields every candidate value — mirrors
`objectCoreAllPairs'`'s `Std.TreeMap.Raw String (List Json)` accumulator, but pre-typed
and pre-validated per field via `aptosFieldValueFromJson`. -/
structure AptosFieldAcc where
  iss           : List String := []
  aud           : List String := []
  uid           : List String := []
  iat           : List ℕ      := []
  emailVerified : List Bool   := []
  nonce         : List String := []
  extraField    : List String := []
  deriving Inhabited

/-- Prepends one more candidate value onto whichever field it belongs to (cheaper than
appending; the resulting per-field order is last-occurrence-first, which nothing depends
on). -/
def AptosFieldAcc.insert : AptosFieldAcc → AptosFieldValue → AptosFieldAcc
  | acc, .iss s           => { acc with iss := s :: acc.iss }
  | acc, .aud s           => { acc with aud := s :: acc.aud }
  | acc, .uid s           => { acc with uid := s :: acc.uid }
  | acc, .iat n           => { acc with iat := n :: acc.iat }
  | acc, .emailVerified b => { acc with emailVerified := b :: acc.emailVerified }
  | acc, .nonce s         => { acc with nonce := s :: acc.nonce }
  | acc, .extraField s    => { acc with extraField := s :: acc.extraField }

/-
`Json.Parser.str`/`Json.Parser.num` bottom out in `partial def`s (`strCore`, `natCore`,
`natCoreNumDigits`) that Lean cannot prove terminating on its own, so it compiles them
to opaque constants (confirmed via `#print`): nothing about their behavior, not even
"the input position never moves backwards", is provable. This namespace locally
reimplements just the string/number lexing loops that were opaque, with real
termination proofs, so that `objectCoreAllPairs'` below can get a genuine
`decreasing_by` proof (no `sorry`, no `partial`) instead of the placeholder it had.
-/
namespace Parser

variable {α β : Type}

/-- `p` never leaves the input position further along than where it started. -/
def NonBacktracking (p : Parser α) : Prop :=
  ∀ (it it' : Sigma String.Pos) (a : α),
    p it = .success it' a →
    it'.2.remainingBytes ≤ it.2.remainingBytes

/-- `p` always advances the input position when it succeeds. -/
def Shrinking (p : Parser α) : Prop :=
  ∀ (it it' : Sigma String.Pos) (a : α),
    p it = .success it' a →
    it'.2.remainingBytes < it.2.remainingBytes

#check Sigma
#check String.Pos
#check Sigma String.Pos

theorem Shrinking.nonBacktracking {p : Parser α} (h : Shrinking p) : NonBacktracking p :=
  fun it it' a hp => Nat.le_of_lt (h it it' a hp)

theorem any_shrinking : Shrinking (α := Char) any := by
  intro it it' c h
  unfold Std.Internal.Parsec.any at h
  simp only [Std.Internal.Parsec.Input.hasNext, Std.Internal.Parsec.Input.next', Std.Internal.Parsec.Input.curr'] at h
  split at h
  · rename_i hh
    injection h with h1 h2
    subst h1
    exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := of_decide_eq_true hh))
  · injection h

theorem any_nonBacktracking : NonBacktracking (α := Char) any :=
  any_shrinking.nonBacktracking

theorem bind_nonBacktracking {f : Parser α} {g : α → Parser β}
    (hf : NonBacktracking f) (hg : ∀ a, NonBacktracking (g a)) :
    NonBacktracking (f >>= g) := by
  intro it it' b h
  simp only [Bind.bind, Std.Internal.Parsec.bind] at h
  split at h
  · rename_i rem a hrem
    exact Nat.le_trans (hg a rem it' b h) (hf it rem a hrem)
  · injection h

theorem bind_shrinking_left {f : Parser α} {g : α → Parser β}
    (hf : Shrinking f) (hg : ∀ a, NonBacktracking (g a)) :
    Shrinking (f >>= g) := by
  intro it it' b h
  simp only [Bind.bind, Std.Internal.Parsec.bind] at h
  split at h
  · rename_i rem a hrem
    exact Nat.lt_of_le_of_lt (hg a rem it' b h) (hf it rem a hrem)
  · injection h

theorem pure_nonBacktracking (a : α) : NonBacktracking (Pure.pure a : Parser α) := by
  intro it it' b h
  simp only [Pure.pure, Std.Internal.Parsec.pure] at h
  injection h with h1 h2
  subst h1
  exact Nat.le_refl _

theorem fail_vacuous (msg : String) : NonBacktracking (α := α) (Std.Internal.Parsec.fail msg) := by
  intro it it' a h
  unfold Std.Internal.Parsec.fail at h
  injection h

theorem hexChar_shrinking : Shrinking Lean.Json.Parser.hexChar := by
  unfold Lean.Json.Parser.hexChar
  apply bind_shrinking_left any_shrinking
  intro c
  split
  · exact pure_nonBacktracking _
  split
  · exact pure_nonBacktracking _
  split
  · exact pure_nonBacktracking _
  · exact fail_vacuous _

theorem finishSurrogatePair_shrinking (low : UInt16) :
    Shrinking (Lean.Json.Parser.finishSurrogatePair low) := by
  unfold Lean.Json.Parser.finishSurrogatePair
  apply bind_shrinking_left any_shrinking
  intro c
  split
  · exact fail_vacuous _
  apply (bind_shrinking_left any_shrinking ?_).nonBacktracking
  intro c'
  split
  · exact fail_vacuous _
  apply (bind_shrinking_left any_shrinking ?_).nonBacktracking
  intro c''
  split
  · exact fail_vacuous _
  apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
  intro u2
  apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
  intro u3
  apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
  intro u4
  dsimp only
  split
  · exact fail_vacuous _
  · split
    · exact pure_nonBacktracking _
    · exact fail_vacuous _

theorem attempt_orElse_nonBacktracking {p q : Parser α}
    (hp : NonBacktracking p) (hq : NonBacktracking q) :
    NonBacktracking (attempt p <|> q) := by
  intro it it' a h
  change Std.Internal.Parsec.orElse (attempt p) (fun _ => q) it = .success it' a at h
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch Std.Internal.Parsec.attempt at h
  rcases hpit : p it with ⟨rem, res⟩ | ⟨rem, err⟩
  · rw [hpit] at h
    dsimp only [Std.Internal.Parsec.pure] at h
    injection h with h1 h2
    subst h1; subst h2
    exact hp it rem res hpit
  · rw [hpit] at h
    dsimp only at h
    rw [if_pos rfl] at h
    exact hq it it' a h

theorem escapedChar_shrinking : Shrinking Lean.Json.Parser.escapedChar := by
  unfold Lean.Json.Parser.escapedChar
  apply bind_shrinking_left any_shrinking
  intro c
  dsimp only
  split <;> try exact pure_nonBacktracking _
  · apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
    intro u1
    apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
    intro u2
    apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
    intro u3
    apply (bind_shrinking_left hexChar_shrinking ?_).nonBacktracking
    intro u4
    dsimp only
    split
    · exact pure_nonBacktracking _
    split
    · split
      · exact attempt_orElse_nonBacktracking (finishSurrogatePair_shrinking _).nonBacktracking (pure_nonBacktracking _)
      · exact pure_nonBacktracking _
    · exact pure_nonBacktracking _
  · exact fail_vacuous _

theorem skip_shrinking : Shrinking skip := by
  intro it it' u h
  unfold Std.Internal.Parsec.skip at h
  simp only [Std.Internal.Parsec.Input.hasNext, Std.Internal.Parsec.Input.next'] at h
  split at h
  · rename_i hh
    injection h with h1 h2
    subst h1
    exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := of_decide_eq_true hh))
  · injection h

theorem peek!_nonBacktracking : NonBacktracking (peek! (ι := Sigma String.Pos) (elem := Char)) := by
  intro it it' c h
  unfold Std.Internal.Parsec.peek! at h
  split at h
  · injection h with h1 h2
    subst h1
    exact Nat.le_refl _
  · injection h

theorem lookahead_nonBacktracking (p : Char → Prop) [DecidablePred p] (desc : String) :
    NonBacktracking (Lean.Json.Parser.lookahead p desc) := by
  unfold Json.Parser.lookahead
  apply bind_nonBacktracking peek!_nonBacktracking
  intro c
  split
  · exact pure_nonBacktracking _
  · exact fail_vacuous _

theorem isEof_nonBacktracking : NonBacktracking (isEof (ι := Sigma String.Pos)) := by
  intro it it' b h
  unfold Std.Internal.Parsec.isEof at h
  injection h with h1 h2
  subst h1
  exact Nat.le_refl _

theorem numSign_nonBacktracking : NonBacktracking Lean.Json.Parser.numSign := by
  unfold Lean.Json.Parser.numSign
  apply bind_nonBacktracking peek!_nonBacktracking
  intro c
  dsimp only
  split
  · apply bind_nonBacktracking skip_shrinking.nonBacktracking
    intro _
    exact pure_nonBacktracking _
  · exact pure_nonBacktracking _

/-- Replacement for the opaque `Json.Parser.natCore`, recursing directly on the
input position (like `Std.Internal.Parsec.String.digitsCore`) so termination is provable. -/
def natCore (acc : Nat) (it : Sigma String.Pos) : ParseResult Nat (Sigma String.Pos) :=
  if h : ¬ it.2.IsAtEnd then
    let c := it.2.get h
    if '0' ≤ c ∧ c ≤ '9' then
      natCore (10*acc + (c.val - '0'.val).toNat) ⟨it.1, it.2.next h⟩
    else
      .success it acc
  else
    .success it acc
termination_by it.2.remainingBytes
decreasing_by exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))

/-- Replacement for the opaque `Json.Parser.natCoreNumDigits`. -/
def natCoreNumDigits (acc digits : Nat) (it : Sigma String.Pos) :
    ParseResult (Nat × Nat) (Sigma String.Pos) :=
  if h : ¬ it.2.IsAtEnd then
    let c := it.2.get h
    if '0' ≤ c ∧ c ≤ '9' then
      natCoreNumDigits (10*acc + (c.val - '0'.val).toNat) (digits+1) ⟨it.1, it.2.next h⟩
    else
      .success it (acc, digits)
  else
    .success it (acc, digits)
termination_by it.2.remainingBytes
decreasing_by exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))

theorem natCore_nonBacktracking (acc : Nat) : NonBacktracking (natCore acc) := by
  revert acc
  intro acc it
  induction acc, it using natCore.induct with
  | case1 acc it h c hr ih =>
    intro it' s heq
    rw [natCore.eq_1, dif_pos h, if_pos hr] at heq
    exact Nat.le_trans (ih it' s heq) (Nat.le_of_lt ((String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))))
  | case2 acc it h c hr =>
    intro it' s heq
    rw [natCore.eq_1, dif_pos h, if_neg hr] at heq
    injection heq with h1 h2
    subst h1
    exact Nat.le_refl _
  | case3 acc it hend =>
    intro it' s heq
    rw [natCore.eq_1, dif_neg hend] at heq
    injection heq with h1 h2
    subst h1
    exact Nat.le_refl _

theorem natCoreNumDigits_nonBacktracking (acc digits : Nat) :
    NonBacktracking (natCoreNumDigits acc digits) := by
  revert acc digits
  intro acc digits it
  induction acc, digits, it using natCoreNumDigits.induct with
  | case1 acc digits it h c hr ih =>
    intro it' r heq
    rw [natCoreNumDigits.eq_1, dif_pos h, if_pos hr] at heq
    exact Nat.le_trans (ih it' r heq) (Nat.le_of_lt ((String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))))
  | case2 acc digits it h c hr =>
    intro it' r heq
    rw [natCoreNumDigits.eq_1, dif_pos h, if_neg hr] at heq
    injection heq with h1 h2
    subst h1
    exact Nat.le_refl _
  | case3 acc digits it hend =>
    intro it' r heq
    rw [natCoreNumDigits.eq_1, dif_neg hend] at heq
    injection heq with h1 h2
    subst h1
    exact Nat.le_refl _

/-- Thin copies of `Json.Parser.natNonZero`/`natMaybeZero`/`natNumDigits`/`nat`/
`numWithDecimals`/`exponent`/`num`, pointed at the local `natCore`/`natCoreNumDigits`
above instead of the opaque originals. Bodies are otherwise identical. -/
def ourNatNonZero : Parser Nat := do
  Parser.lookahead (fun c => '1' <= c && c <= '9') "1-9"
  natCore 0

def ourNatNumDigits : Parser (Nat × Nat) := do
  Parser.lookahead (fun c => '0' <= c && c <= '9') "digit"
  natCoreNumDigits 0 0

def ourNatMaybeZero : Parser Nat := do
  Parser.lookahead (fun c => '0' <= c && c <= '9') "0-9"
  natCore 0

def ourNat : Parser Nat := do
  let c ← peek!
  if c == '0' then
    skip
    return 0
  else
    ourNatNonZero

def ourNumWithDecimals : Parser Lean.JsonNumber := do
  let sign ← Lean.Json.Parser.numSign
  let whole ← ourNat
  if ← isEof then
    pure <| Lean.JsonNumber.fromInt (sign * whole)
  else
    let c ← peek!
    if c == '.' then
      skip
      let (n, d) ← ourNatNumDigits
      if d > USize.size then fail "too many decimals"
      let mantissa' := sign * (whole * (10^d : Nat) + n)
      let exponent' := d
      pure <| Lean.JsonNumber.mk mantissa' exponent'
    else
      pure <| Lean.JsonNumber.fromInt (sign * whole)

def ourExponent (value : Lean.JsonNumber) : Parser Lean.JsonNumber := do
  if ← isEof then
    return value
  else
    let c ← peek!
    if c == 'e' || c == 'E' then
      skip
      let c ← peek!
      if c == '-' then
        skip
        let n ← ourNatMaybeZero
        return value.shiftr n
      else
        if c = '+' then skip
        let n ← ourNatMaybeZero
        if n > USize.size then fail "exp too large"
        return value.shiftl n
    else
      return value

def ourNum : Parser Lean.JsonNumber := do
  let res : Lean.JsonNumber ← ourNumWithDecimals
  ourExponent res

theorem ourNatNonZero_nonBacktracking : NonBacktracking ourNatNonZero := by
  unfold ourNatNonZero
  apply bind_nonBacktracking (lookahead_nonBacktracking _ _)
  intro _
  exact natCore_nonBacktracking 0

theorem ourNatNumDigits_nonBacktracking : NonBacktracking ourNatNumDigits := by
  unfold ourNatNumDigits
  apply bind_nonBacktracking (lookahead_nonBacktracking _ _)
  intro _
  exact natCoreNumDigits_nonBacktracking 0 0

theorem ourNatMaybeZero_nonBacktracking : NonBacktracking ourNatMaybeZero := by
  unfold ourNatMaybeZero
  apply bind_nonBacktracking (lookahead_nonBacktracking _ _)
  intro _
  exact natCore_nonBacktracking 0

theorem ourNat_nonBacktracking : NonBacktracking ourNat := by
  unfold ourNat
  apply bind_nonBacktracking peek!_nonBacktracking
  intro c
  dsimp only
  split
  · apply bind_nonBacktracking skip_shrinking.nonBacktracking
    intro _
    exact pure_nonBacktracking _
  · exact ourNatNonZero_nonBacktracking

theorem ourNumWithDecimals_nonBacktracking : NonBacktracking ourNumWithDecimals := by
  unfold ourNumWithDecimals
  apply bind_nonBacktracking numSign_nonBacktracking
  intro sign
  apply bind_nonBacktracking ourNat_nonBacktracking
  intro whole
  apply bind_nonBacktracking isEof_nonBacktracking
  intro b
  dsimp only
  split
  · exact pure_nonBacktracking _
  · apply bind_nonBacktracking peek!_nonBacktracking
    intro c
    dsimp only
    split
    · apply bind_nonBacktracking skip_shrinking.nonBacktracking
      intro _
      apply bind_nonBacktracking ourNatNumDigits_nonBacktracking
      intro nd
      dsimp only
      split
      · exact fail_vacuous _
      · exact pure_nonBacktracking _
    · exact pure_nonBacktracking _

theorem ourExponent_nonBacktracking (value : Lean.JsonNumber) : NonBacktracking (ourExponent value) := by
  unfold ourExponent
  apply bind_nonBacktracking isEof_nonBacktracking
  intro b
  dsimp only
  split
  · exact pure_nonBacktracking _
  · apply bind_nonBacktracking peek!_nonBacktracking
    intro c
    dsimp only
    split
    · apply bind_nonBacktracking skip_shrinking.nonBacktracking
      intro _
      apply bind_nonBacktracking peek!_nonBacktracking
      intro c2
      dsimp only
      split
      · apply bind_nonBacktracking skip_shrinking.nonBacktracking
        intro _
        apply bind_nonBacktracking ourNatMaybeZero_nonBacktracking
        intro n
        exact pure_nonBacktracking _
      · split <;>
        · apply bind_nonBacktracking
          · first | exact skip_shrinking.nonBacktracking | exact pure_nonBacktracking _
          intro _
          apply bind_nonBacktracking ourNatMaybeZero_nonBacktracking
          intro n
          dsimp only
          split
          · exact fail_vacuous _
          · exact pure_nonBacktracking _
    · exact pure_nonBacktracking _

theorem ourNum_nonBacktracking : NonBacktracking ourNum := by
  unfold ourNum
  apply bind_nonBacktracking ourNumWithDecimals_nonBacktracking
  intro res
  exact ourExponent_nonBacktracking res

/-- Replacement for the private `Std.Internal.Parsec.String.skipWs`/`ws` (private, so
inaccessible for proofs from this file), recursing directly on the input position. -/
def skipWsCore (it : Sigma String.Pos) : Sigma String.Pos :=
  if h : ¬ it.2.IsAtEnd then
    let c := it.2.get h
    if c = '\t' ∨ c = '\n' ∨ c = '\x0d' ∨ c = ' ' then
      skipWsCore ⟨it.1, it.2.next h⟩
    else
      it
  else
    it
termination_by it.2.remainingBytes
decreasing_by exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))

def ws' : Parser Unit := fun it => .success (skipWsCore it) ()

theorem skipWsCore_nonBacktracking (it : Sigma String.Pos) :
    (skipWsCore it).2.remainingBytes ≤ it.2.remainingBytes := by
  induction it using skipWsCore.induct with
  | case1 it h c hws ih =>
    rw [skipWsCore.eq_1, dif_pos h, if_pos hws]
    exact Nat.le_trans ih (Nat.le_of_lt ((String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))))
  | case2 it h c hws =>
    rw [skipWsCore.eq_1, dif_pos h, if_neg hws]
  | case3 it hend =>
    rw [skipWsCore.eq_1, dif_neg hend]

theorem ws'_nonBacktracking : NonBacktracking ws' := by
  intro it it' u h
  unfold ws' at h
  injection h with h1 h2
  subst h1
  exact skipWsCore_nonBacktracking it

theorem pstring_nonBacktracking (s : String) : NonBacktracking (pstring s) := by
  intro it it' r h
  unfold Std.Internal.Parsec.String.pstring at h
  split at h
  · injection h with h1 h2
    subst h1
    apply (String.Pos.le_iff_remainingBytes_le _ _).mp
    exact String.Pos.le_nextn
  · injection h

/-- `String.Pos.nextn` clamps at `endPos`, so it only strictly advances when there's at least
one step to take (`n ≠ 0`) starting from a position that isn't already the end. -/
theorem Pos_lt_nextn {str : String} {p : str.Pos} {n : Nat} (hn : n ≠ 0) (h : p ≠ str.endPos) :
    p < p.nextn n := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  show p < p.nextn n'.succ
  unfold String.Pos.nextn
  rw [String.Pos.lt_ofToSlice_iff]
  have hSlice : p.toSlice ≠ str.toSlice.endPos := by
    rw [String.endPos_toSlice]
    exact fun heq => h (String.Pos.toSlice_inj.mp heq)
  show p.toSlice < String.Slice.Pos.nextn p.toSlice n'.succ
  rw [String.Slice.Pos.nextn, dif_pos hSlice]
  exact Std.lt_of_lt_of_le String.Slice.Pos.lt_next String.Slice.Pos.le_nextn

theorem pstring_shrinking (s : String) (hs : s ≠ "") : Shrinking (pstring s) := by
  intro it it' r h
  unfold Std.Internal.Parsec.String.pstring at h
  split at h
  · rename_i hstart
    injection h with h1 h2
    subst h1
    apply (String.Pos.lt_iff_remainingBytes_lt _ _).mp
    have hlen : s.utf8ByteSize ≤ it.2.remainingBytes := by
      simp only [String.Slice.startsWith, String.Slice.Pattern.ForwardPattern.startsWith,
        String.Slice.Pattern.ForwardSliceSearcher.startsWith] at hstart
      split at hstart
      · rename_i hle
        simp only [String.utf8ByteSize_sliceFrom, String.Pos.remainingBytes_eq] at hle ⊢
        simpa using hle
      · simp at hstart
    have hs0 : s.utf8ByteSize ≠ 0 :=
      fun h0 => hs (String.utf8ByteSize_eq_zero_iff.mp h0)
    have hne : it.2 ≠ it.1.endPos := by
      intro heq
      have hend : it.2.remainingBytes = 0 := by
        rw [heq, String.Pos.remainingBytes_eq, String.offset_endPos, String.byteIdx_rawEndPos]
        omega
      omega
    have hlenne : s.length ≠ 0 := fun h0 => hs (String.length_eq_zero_iff.mp h0)
    exact Pos_lt_nextn hlenne hne
  · injection h

theorem skipString_nonBacktracking (s : String) : NonBacktracking (skipString s) := by
  unfold Std.Internal.Parsec.String.skipString
  apply bind_nonBacktracking (pstring_nonBacktracking s)
  intro _
  exact pure_nonBacktracking _

theorem skipString_shrinking (s : String) (hs : s ≠ "") : Shrinking (skipString s) := by
  unfold Std.Internal.Parsec.String.skipString
  apply bind_shrinking_left (pstring_shrinking s hs)
  intro _
  exact pure_nonBacktracking _

/-- Replacement for the opaque `Json.Parser.strCore`, recursing directly on the input
position; `Json.Parser.escapedChar`/`hexChar`/`finishSurrogatePair` are reused as-is
since they're ordinary (non-`partial`, non-recursive) defs, not opaque. -/
def strCore (acc : String) (it : Sigma String.Pos) : ParseResult String (Sigma String.Pos) :=
  if h : ¬ it.2.IsAtEnd then
    let c := it.2.get h
    if c == '"' then
      .success ⟨it.1, it.2.next h⟩ acc
    else if c == '\\' then
      match hEsc : Lean.Json.Parser.escapedChar ⟨it.1, it.2.next h⟩ with
      | .success it' c' => strCore (acc.push c') it'
      | .error it' err => .error it' err
    else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
      strCore (acc.push c) ⟨it.1, it.2.next h⟩
    else
      .error it (.other "unexpected character in string")
  else
    .error it .eof
termination_by it.2.remainingBytes
decreasing_by
  all_goals try exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))
  all_goals (exact Nat.lt_of_le_of_lt (escapedChar_shrinking.nonBacktracking _ _ _ hEsc) ((String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))))

/-- Replacement for `Json.Parser.str`. -/
def str : Parser String := strCore ""

theorem strCore_nonBacktracking :
    ∀ (acc : String) (it : Sigma String.Pos),
      ∀ it' s, strCore acc it = .success it' s → it'.2.remainingBytes ≤ it.2.remainingBytes := by
  intro acc it
  induction acc, it using strCore.induct with
  | case1 acc it h c hquote =>
    intro it' s heq
    rw [strCore.eq_1, dif_pos h, if_pos hquote] at heq
    injection heq with h1 h2
    subst h1
    exact Nat.le_of_lt ((String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h)))
  | case2 acc it h c hne1 hbs it0 c0 hEscEq ih =>
    intro it' s heq
    rw [strCore.eq_1, dif_pos h, if_neg hne1, if_pos hbs] at heq
    rw [hEscEq] at heq
    have hb1 : it0.2.remainingBytes ≤ (it.snd.next h).remainingBytes :=
      escapedChar_shrinking.nonBacktracking _ _ _ hEscEq
    have hb2 : (it.snd.next h).remainingBytes < it.snd.remainingBytes :=
      (String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))
    exact Nat.le_trans (ih it' s heq) (Nat.le_of_lt (Nat.lt_of_le_of_lt hb1 hb2))
  | case3 acc it h c hne1 hbs it0 err hEscEq =>
    intro it' s heq
    rw [strCore.eq_1, dif_pos h, if_neg hne1, if_pos hbs] at heq
    rw [hEscEq] at heq
    injection heq
  | case4 acc it h c hne1 hne2 hrange ih =>
    intro it' s heq
    rw [strCore.eq_1, dif_pos h, if_neg hne1, if_neg hne2, if_pos hrange] at heq
    exact Nat.le_trans (ih it' s heq) (Nat.le_of_lt ((String.Pos.lt_iff_remainingBytes_lt _ _).mp (String.Pos.lt_next (h := h))))
  | case5 acc it h c hne1 hne2 hrangeneg =>
    intro it' s heq
    rw [strCore.eq_1, dif_pos h, if_neg hne1, if_neg hne2, if_neg hrangeneg] at heq
    injection heq
  | case6 acc it hend =>
    intro it' s heq
    rw [strCore.eq_1, dif_neg hend] at heq
    injection heq

theorem str_nonBacktracking : NonBacktracking str :=
  fun it it' s h => strCore_nonBacktracking "" it it' s h

/-- Parses a JSON string including its surrounding quotes: the opening `"` plus
everything `str` consumes (which already includes the matching closing `"`). -/
def quotedStr : Parser String := do
  skipString "\""
  str

theorem quotedStr_shrinking : Shrinking quotedStr := by
  unfold quotedStr
  apply bind_shrinking_left (skipString_shrinking "\"" (by decide))
  intro _
  exact str_nonBacktracking

/--
Like `Json.Parser.anyCore`, but only parses flat JSON values (strings, numbers,
booleans, null), never arrays or objects. Since it never recurses into itself,
unlike `anyCore` it does not need to be `partial`.
-/
def jsonFlatValue : Parser Lean.Json := do
  let c ← peek!
  if c == '\"' then
    let s ← quotedStr
    ws'
    return Lean.Json.str s
  else if c == 'f' then
    skipString "false"; ws'
    return Lean.Json.bool false
  else if c == 't' then
    skipString "true"; ws'
    return Lean.Json.bool true
  else if c == 'n' then
    skipString "null"; ws'
    return Lean.Json.null
  else if c == '-' || ('0' <= c && c <= '9') then
    let n ← ourNum
    ws'
    return Lean.Json.num n
  else
    fail "unexpected input"

-- { "...." ... { ... } }
#check Parser.objectCore
-- def parseJson' (isEscaped isQuoted : Bool) : Parser Unit := do
--   pure ()

theorem jsonFlatValue_nonBacktracking : NonBacktracking jsonFlatValue := by
  unfold jsonFlatValue
  apply bind_nonBacktracking peek!_nonBacktracking
  intro c
  dsimp only
  split
  · apply bind_nonBacktracking quotedStr_shrinking.nonBacktracking
    intro s
    apply bind_nonBacktracking ws'_nonBacktracking
    intro _
    exact pure_nonBacktracking _
  · split
    · apply bind_nonBacktracking (skipString_nonBacktracking _)
      intro _
      apply bind_nonBacktracking ws'_nonBacktracking
      intro _
      exact pure_nonBacktracking _
    · split
      · apply bind_nonBacktracking (skipString_nonBacktracking _)
        intro _
        apply bind_nonBacktracking ws'_nonBacktracking
        intro _
        exact pure_nonBacktracking _
      · split
        · apply bind_nonBacktracking (skipString_nonBacktracking _)
          intro _
          apply bind_nonBacktracking ws'_nonBacktracking
          intro _
          exact pure_nonBacktracking _
        · split
          · apply bind_nonBacktracking ourNum_nonBacktracking
            intro n
            apply bind_nonBacktracking ws'_nonBacktracking
            intro _
            exact pure_nonBacktracking _
          · exact fail_vacuous _

theorem bind_shrinking_of_nonBacktracking_shrinking {f : Parser α} {g : α → Parser β}
    (hf : NonBacktracking f) (hg : ∀ a, Shrinking (g a)) :
    Shrinking (f >>= g) := by
  intro it it' b h
  simp only [Bind.bind, Std.Internal.Parsec.bind] at h
  split at h
  · rename_i rem a hrem
    exact Nat.lt_of_lt_of_le (hg a rem it' b h) (hf it rem a hrem)
  · injection h

/-- One `"key" : value` pair (not including the trailing `}`/`,`/separator
character, which `objectCoreAllPairs'` now parses itself right after calling
this). Split out from `objectCoreAllPairs'` so it can stay ordinary
`do`-notation (no termination concerns, since it never recurses), while still
exposing the one guaranteed-shrinking step (the leading `quotedStr`, which
consumes the pair's opening `"`) that `objectCoreAllPairs'` relies on for its
own termination proof. -/
def parseOnePair : Parser (String × Lean.Json) := do
  let k ← quotedStr
  ws'
  skipString ":"
  ws'
  let v ← jsonFlatValue
  pure (k, v)

-- #check Parser.anyCore
#check Parser.anyOfFn

theorem parseOnePair_shrinking : Shrinking parseOnePair := by
  unfold parseOnePair
  apply bind_shrinking_left quotedStr_shrinking
  intro _
  apply bind_nonBacktracking ws'_nonBacktracking
  intro _
  apply bind_nonBacktracking (skipString_nonBacktracking _)
  intro _
  apply bind_nonBacktracking ws'_nonBacktracking
  intro _
  apply bind_nonBacktracking jsonFlatValue_nonBacktracking
  intro v
  exact pure_nonBacktracking _

/--
Parse a list of one or more key-value pairs followed by a "}".
Implemented like `Json.Parser.objectCore`, but it keeps all the claims from the
top level that share the same key.
-/
def objectCoreAllPairs' (acc : Std.TreeMap.Raw String (List Lean.Json))
    (it : Sigma String.Pos) :
    ParseResult (Std.TreeMap.Raw String (List Lean.Json)) (Sigma String.Pos) :=
  match hp : parseOnePair it with
  | .error it' err => .error it' err
  | .success it' (k, v) =>
    match hc : any it' with
    | .error it'' err => .error it'' err
    | .success it'' c =>
      let acc' := acc.mergeWith (fun _ v₁ v₂ ↦ v₁ ++ v₂) {(k, [v])}
      match c with
      | '}' => .success (skipWsCore it'') acc'
      | ',' => objectCoreAllPairs' acc' (skipWsCore it'')
      | _ => .error it'' (.other "unexpected character in object")
termination_by it.2.remainingBytes
decreasing_by
  exact Nat.lt_of_le_of_lt (skipWsCore_nonBacktracking it'')
    (Nat.lt_of_le_of_lt (any_nonBacktracking _ _ _ hc) (parseOnePair_shrinking _ _ _ hp))

/-- Like `parseOnePair`, but instead of returning the parsed value verbatim, immediately
dispatches it through `aptosFieldValueFromJson` — fusing `AptosPayload`'s per-field type
and semantic checks into the point where each pair's value is parsed. Returns `[]` for a
key that names none of `AptosPayload`'s fields. -/
def parseOneAptosPair (uidKey : UidKey) (extraFieldKey : String) :
    Parser (List AptosFieldValue) := do
  let k ← quotedStr
  ws'
  skipString ":"
  ws'
  let v ← jsonFlatValue
  match aptosFieldValueFromJson uidKey extraFieldKey k v with
  | .ok vs => pure vs
  | .error e => fail e

theorem parseOneAptosPair_shrinking (uidKey : UidKey) (extraFieldKey : String) :
    Shrinking (parseOneAptosPair uidKey extraFieldKey) := by
  unfold parseOneAptosPair
  apply bind_shrinking_left quotedStr_shrinking
  intro k
  apply bind_nonBacktracking ws'_nonBacktracking
  intro _
  apply bind_nonBacktracking (skipString_nonBacktracking _)
  intro _
  apply bind_nonBacktracking ws'_nonBacktracking
  intro _
  apply bind_nonBacktracking jsonFlatValue_nonBacktracking
  intro v
  dsimp only
  cases aptosFieldValueFromJson uidKey extraFieldKey k v with
  | ok vs => exact pure_nonBacktracking _
  | error e => exact fail_vacuous _

/-- Like `objectCoreAllPairs'`, but accumulates typed, per-field-validated
`AptosFieldValue`s (via `parseOneAptosPair`) into an `AptosFieldAcc` instead of a
generic `Std.TreeMap.Raw String (List Json)`. -/
def objectCoreAllAptosPairs' (uidKey : UidKey) (extraFieldKey : String) (acc : AptosFieldAcc)
    (it : Sigma String.Pos) : ParseResult AptosFieldAcc (Sigma String.Pos) :=
  match hp : parseOneAptosPair uidKey extraFieldKey it with
  | .error it' err => .error it' err
  | .success it' vs =>
    match hc : any it' with
    | .error it'' err => .error it'' err
    | .success it'' c =>
      let acc' := vs.foldl AptosFieldAcc.insert acc
      match c with
      | '}' => .success (skipWsCore it'') acc'
      | ',' => objectCoreAllAptosPairs' uidKey extraFieldKey acc' (skipWsCore it'')
      | _ => .error it'' (.other "unexpected character in object")
termination_by it.2.remainingBytes
decreasing_by
  exact Nat.lt_of_le_of_lt (skipWsCore_nonBacktracking it'')
    (Nat.lt_of_le_of_lt (any_nonBacktracking _ _ _ hc)
      (parseOneAptosPair_shrinking uidKey extraFieldKey _ _ _ hp))

end Parser

/-- All ways of picking one value for each key from its list of candidate values
-/
def keyValueAlts : List (String × List Json) → List (List (String × Json))
  | [] => [[]]
  | (k, vs) :: rest =>
    let restAlts := keyValueAlts rest
    vs.flatMap (fun v => restAlts.map (fun r => (k, v) :: r))

/-- Like `Json.Parser.any`, but restricted to flat JSON objects (values are not
themselves JSON objects/arrays) and nondeterministic in the presence of duplicate keys
 -/
def anyFlatNondet : Parser (List Json) := do
  Parser.ws'
  skipString "{"; Parser.ws'
  let c ← peek!
  let alts ←
    if c == '}' then
      skip; Parser.ws'
      pure [Json.obj ∅]
    else do
      let pairs ← Parser.objectCoreAllPairs' ∅
      let alts := keyValueAlts pairs.toList
      pure (alts.map (fun kvs => Json.obj (kvs.foldl (fun m (k, v) => m.insert k v) ∅)))
  eof
  pure alts

/-- Like `anyFlatNondet`, but scans the object's pairs straight into an `AptosFieldAcc`
via `Parser.objectCoreAllAptosPairs'`, fusing `AptosPayload`'s per-field type/semantic
checks into the scan instead of building a generic `Json` first. -/
def aptosFieldsFromJson (uidKey : UidKey) (extraFieldKey : String) : Parser AptosFieldAcc := do
  Parser.ws'
  skipString "{"; Parser.ws'
  let c ← peek!
  let acc ←
    if c == '}' then
      skip; Parser.ws'
      pure {}
    else
      Parser.objectCoreAllAptosPairs' uidKey extraFieldKey {}
  eof
  pure acc

/-- Turns a fully-scanned `AptosFieldAcc` into every candidate `AptosPayload` implied by
its duplicate-key combinatorics (mirroring `keyValueAlts`), after checking every field
was present at least once, and applying the one remaining cross-field check
(`uidKey == .email → email_verified`) that needs the whole record and so couldn't be
fused into `aptosFieldValueFromJson`. -/
def AptosFieldAcc.toPayloads (uidKey : UidKey) (extraFieldKey : String) (acc : AptosFieldAcc) :
    Except String (List AptosPayload) := do
  if acc.iss.isEmpty then throw "The field (iss) is required."
  if acc.aud.isEmpty then throw "The field (aud) is required."
  if acc.uid.isEmpty then throw s!"The field ({uidKey.fieldName}) is required."
  if acc.iat.isEmpty then throw "The field (iat) is required."
  if acc.emailVerified.isEmpty then throw "The field (email_verified) is required."
  if acc.nonce.isEmpty then throw "The field (nonce) is required."
  if acc.extraField.isEmpty then throw s!"The field ({extraFieldKey}) is required."

  let candidates : List AptosPayload :=
    acc.iss.flatMap fun iss =>
    acc.aud.flatMap fun aud =>
    acc.uid.flatMap fun uid =>
    acc.iat.flatMap fun iat =>
    acc.emailVerified.flatMap fun email_verified =>
    acc.nonce.flatMap fun nonce =>
    acc.extraField.map fun extra_field =>
      { iss, aud, uid, iat, email_verified, nonce, extra_field : AptosPayload }

  candidates.mapM fun p => do
    if uidKey == UidKey.email && p.email_verified = false then
      throw s!"The user id key is email, but email_verified is false"
    return p

def payloads_from_json_string
  (uidKey : UidKey)
  (extraFieldKey : String)
  (s: String) :
  Except String (List AptosPayload)
:= do
  let acc ← Parser.run (aptosFieldsFromJson uidKey extraFieldKey) s
  acc.toPayloads uidKey extraFieldKey

/-
  json accepted by the constraint system →

  one of the results by the parser
-/

def String.quote s := "\"" ++ s ++ "\""
def claim (k v : String) := k.quote ++ " : " ++ v

def dummyNonce : String := "159196287899032468733794277330513742183729069551015157917"

def jsonInput (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

def jsonInput_no_iss (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

def jsonInput_duplicated_iss1 (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "iss" "dummy iss 2".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

/-- Same shape as `jsonInput`, but with an empty `nonce`. -/
def jsonInput_empty_nonce (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" "".quote
  ]
  ++ " }"

def jsonInput_no_aud (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

def jsonInput_no_sub (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

def jsonInput_no_email_verified : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

def jsonInput_no_nonce (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified
  ]
  ++ " }"

/-- `iat` is a non-integer JSON number. -/
def jsonInput_bad_iat (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138.5",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

/-- `exp` is a JSON string instead of a number. -/
def jsonInput_string_exp (emailVerified : String) : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739".quote,
    claim "shoe_size" "40".quote,
    claim "email_verified" emailVerified,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

/-- Duplicated `email_verified`: one occurrence valid (`true`), the other invalid (not
`true`/`false`/`"true"`/`"false"`). -/
def jsonInput_duplicated_email_verified_conflict : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" "true",
    claim "email_verified" "nope".quote,
    claim "nonce" dummyNonce.quote
  ]
  ++ " }"

/-- Duplicated `nonce`: one occurrence all-digits (valid), the other containing a letter
(invalid). -/
def jsonInput_duplicated_nonce_conflict : String :=
  "{ " ++
  String.intercalate ", "
  [
    claim "iss" "dummy iss".quote,
    claim "aud" "dummy aud".quote,
    claim "sub" "dummy sub".quote,
    claim "email" "dummy email".quote,
    claim "iat" "1719866138",
    claim "exp" "1719869739",
    claim "shoe_size" "40".quote,
    claim "email_verified" "true",
    claim "nonce" dummyNonce.quote,
    claim "nonce" "abc123".quote
  ]
  ++ " }"

#eval payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "true"))

example : -- `email_verified` is the bool `true`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

example : -- duplicated `iss`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput_duplicated_iss1 (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss 2",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      , { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide


example : -- `email_verified` is the string `"true"`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

example : -- `email_verified` is the bool `false`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "false"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := false,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

example : -- user id key is `email`, but `email_verified` is `"false"`
  (payloads_from_json_string
    (uidKey := .email)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "false".quote))
  ).toOption
    == .none
:= by native_decide

-- example : -- iat + expHorizon ≤ exp
--   (payloads_from_json_string
--     (uidKey := .email)
--     (extraFieldKey := "shoe_size")
--     -- (expHorizon := 1)
--     (jsonInput (emailVerified := "true"))
--   ).toOption
--     = .none
--   := by native_decide

example : -- extra field exists, it's "email"
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "email")
    -- (expHorizon := 6002)
    (jsonInput (emailVerified := "true".quote))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "dummy email" }
      ]
:= by native_decide

example : -- extra field doesn't exist
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "nonexistent")
    -- (expHorizon := 6002)
    (jsonInput (emailVerified := "true".quote))
  ).toOption
    = .none
  := by native_decide

example : -- `extraFieldKey` colliding with `uidKey.fieldName` (both "sub"): the same JSON
          -- value populates both `uid` and `extra_field`, matching what independently
          -- calling `getObjValAs?` twice against the same key would give
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "sub")
    (jsonInput (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "dummy sub" }
      ]
:= by native_decide

example : -- missing iss field
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "email")
    -- (expHorizon := 6002)
    (jsonInput_no_iss (emailVerified := "true"))
  ).toOption
    = none
  := by native_decide

example : -- with no duplicate keys, `anyFlatNondet` returns exactly one alternative
  (Parser.run anyFlatNondet (jsonInput (emailVerified := "true"))).toOption.map List.length
    = some 1
  := by native_decide

example : -- a duplicated `iss` field yields exactly the two alternatives implied by its
          -- two occurrences, one per possible "winner"
  ((Parser.run anyFlatNondet (jsonInput_duplicated_iss1 (emailVerified := "true"))).toOption.map
    (fun alts =>
      alts.length == 2 &&
      alts.any (fun j => (j.getObjValAs? String "iss").toOption == some "dummy iss") &&
      alts.any (fun j => (j.getObjValAs? String "iss").toOption == some "dummy iss 2")))
    = some true
  := by native_decide

-- ---------------------------------------------------------------------------
-- A. Regression tests for the `eof` fix (trailing garbage after the parsed
-- object is now rejected) and the empty-`nonce` fix.
-- ---------------------------------------------------------------------------

example : -- trailing garbage after the closing `}` is rejected
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    ((jsonInput (emailVerified := "true")) ++ " garbage")
  ).toOption
    == .none
:= by native_decide

example : -- trailing non-whitespace after `{}` is rejected at the `Parser.run` level
  (Parser.run anyFlatNondet "{} trailing").toOption == none
:= by native_decide

example : -- whitespace-only trailing input after `{}` is still accepted
  (Parser.run anyFlatNondet "{}   \t\n").toOption == some [Json.obj ∅]
:= by native_decide

example : -- an empty `nonce` is rejected
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput_empty_nonce (emailVerified := "true"))
  ).toOption
    == .none
:= by native_decide

-- ---------------------------------------------------------------------------
-- B. Number lexer (`Parser.ourNum`) — parity with `Lean.Json.parse`, and
-- rejections of malformed literals.
-- ---------------------------------------------------------------------------

example : -- the local number lexer agrees with `Json.parse` across a range of literal forms
  (Parser.run Parser.jsonFlatValue "0").toOption == (Lean.Json.parse "0").toOption
  ∧ (Parser.run Parser.jsonFlatValue "-0").toOption == (Lean.Json.parse "-0").toOption
  ∧ (Parser.run Parser.jsonFlatValue "123").toOption == (Lean.Json.parse "123").toOption
  ∧ (Parser.run Parser.jsonFlatValue "1.5").toOption == (Lean.Json.parse "1.5").toOption
  ∧ (Parser.run Parser.jsonFlatValue "1e10").toOption == (Lean.Json.parse "1e10").toOption
  ∧ (Parser.run Parser.jsonFlatValue "1E-3").toOption == (Lean.Json.parse "1E-3").toOption
  ∧ (Parser.run Parser.jsonFlatValue "1.5e+2").toOption == (Lean.Json.parse "1.5e+2").toOption
  ∧ (Parser.run Parser.jsonFlatValue "0.0").toOption == (Lean.Json.parse "0.0").toOption
:= by native_decide

example : -- malformed numbers are rejected by the local number lexer
  (Parser.run Parser.jsonFlatValue "1.").toOption == none
  ∧ (Parser.run Parser.jsonFlatValue ".").toOption == none
  ∧ (Parser.run Parser.jsonFlatValue "-").toOption == none
:= by native_decide

example : -- a number with a disallowed leading zero (e.g. `01`) is rejected once embedded in an
          -- object: the parser reads just the `0`, then misreads the leftover `1` as the
          -- expected `}`/`,` separator and errors out
  (Parser.run anyFlatNondet "{\"a\":01}").toOption == none
:= by native_decide

-- ---------------------------------------------------------------------------
-- C. String lexer (`Parser.str`) — parity with `Json.parse` on escapes, and
-- rejections. Test strings are built with `String.ofList [...]` (explicit `Char`
-- literals) rather than doubly-escaped string literals, to avoid mistakes in
-- counting backslashes.
-- ---------------------------------------------------------------------------

example : -- the local string lexer agrees with `Json.parse` on the empty string
  (Parser.run Parser.jsonFlatValue "\"\"").toOption == (Lean.Json.parse "\"\"").toOption
:= by native_decide

example : -- the local string lexer agrees with `Json.parse` on each basic escape sequence
  let bslash := String.ofList ['"', '\\', '\\', '"']
  let quote  := String.ofList ['"', '\\', '"', '"']
  let slash  := String.ofList ['"', '\\', '/', '"']
  let bksp   := String.ofList ['"', '\\', 'b', '"']
  let ff     := String.ofList ['"', '\\', 'f', '"']
  let cr     := String.ofList ['"', '\\', 'r', '"']
  (Parser.run Parser.jsonFlatValue bslash).toOption == (Lean.Json.parse bslash).toOption
  ∧ (Parser.run Parser.jsonFlatValue quote).toOption == (Lean.Json.parse quote).toOption
  ∧ (Parser.run Parser.jsonFlatValue slash).toOption == (Lean.Json.parse slash).toOption
  ∧ (Parser.run Parser.jsonFlatValue bksp).toOption == (Lean.Json.parse bksp).toOption
  ∧ (Parser.run Parser.jsonFlatValue ff).toOption == (Lean.Json.parse ff).toOption
  ∧ (Parser.run Parser.jsonFlatValue cr).toOption == (Lean.Json.parse cr).toOption
:= by native_decide

example : -- a valid surrogate pair (`\ud83d\ude00` = 😀) decodes the same way as `Json.parse`
  let s := String.ofList ['"', '\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'd', 'e', '0', '0', '"']
  (Parser.run Parser.jsonFlatValue s).toOption == (Lean.Json.parse s).toOption
  ∧ (Parser.run Parser.jsonFlatValue s).toOption == some (Json.str "😀")
:= by native_decide

example : -- a lone high surrogate not followed by a valid low surrogate falls back to U+FFFD,
          -- without swallowing the following character, matching `Json.parse`
  let s := String.ofList ['"', '\\', 'u', 'd', '8', '0', '0', 'A', '"']
  (Parser.run Parser.jsonFlatValue s).toOption == (Lean.Json.parse s).toOption
  ∧ (Parser.run Parser.jsonFlatValue s).toOption == some (Json.str "\ufffdA")
:= by native_decide

example : -- an unescaped, raw multi-byte UTF-8 character is accepted directly (no `\u` needed)
  let s := String.ofList ['"', 'h', 'é', 'l', 'l', 'o', '"']
  (Parser.run Parser.jsonFlatValue s).toOption == (Lean.Json.parse s).toOption
  ∧ (Parser.run Parser.jsonFlatValue s).toOption == some (Json.str "héllo")
:= by native_decide

example : -- an unterminated string (no closing quote) is rejected
  let s := String.ofList ['"', 'a', 'b', 'c']
  (Parser.run Parser.jsonFlatValue s).toOption == none
:= by native_decide

example : -- a raw, unescaped control character (e.g. a literal tab) inside a string is rejected
  let s := String.ofList ['"', '\t', '"']
  (Parser.run Parser.jsonFlatValue s).toOption == none
:= by native_decide

example : -- an unrecognized escape character (e.g. `\a`) is rejected
  let s := String.ofList ['"', '\\', 'a', '"']
  (Parser.run Parser.jsonFlatValue s).toOption == none
:= by native_decide

example : -- an invalid hex digit in a `\u` escape is rejected
  let s := String.ofList ['"', '\\', 'u', 'Z', 'Z', 'Z', 'Z', '"']
  (Parser.run Parser.jsonFlatValue s).toOption == none
:= by native_decide

-- ---------------------------------------------------------------------------
-- D. Object-level parsing (`anyFlatNondet` / `objectCoreAllPairs'`).
-- ---------------------------------------------------------------------------

example : -- an empty object parses to a single alternative: the empty object
  (Parser.run anyFlatNondet "{}").toOption == some [Json.obj ∅]
:= by native_decide

example : -- internal whitespace (tabs/newlines) around the braces is tolerated
  (Parser.run anyFlatNondet "{ \t\n }").toOption == some [Json.obj ∅]
:= by native_decide

example : -- whitespace (space/tab/newline/CR) is tolerated around every separator, and the
          -- parsed values are still correct
  ((Parser.run anyFlatNondet "{\t\"a\"\n:\r1 ,\t\"b\"\n:\r2\n}").toOption.map List.length
    = some 1)
  ∧ (((Parser.run anyFlatNondet "{\t\"a\"\n:\r1 ,\t\"b\"\n:\r2\n}").toOption.bind List.head?).bind
      (fun j => (j.getObjValAs? Nat "a").toOption) = some 1)
:= by native_decide

example : -- a trailing comma before `}` is rejected
  (Parser.run anyFlatNondet "{\"a\":1,}").toOption == none
:= by native_decide

example : -- a missing comma between two pairs is rejected
  (Parser.run anyFlatNondet "{\"a\":1 \"b\":2}").toOption == none
:= by native_decide

example : -- a missing colon after a key is rejected
  (Parser.run anyFlatNondet "{\"a\" 1}").toOption == none
:= by native_decide

example : -- a nested object value is rejected (`anyFlatNondet` only supports flat values)
  (Parser.run anyFlatNondet "{\"a\":{\"b\":1}}").toOption == none
:= by native_decide

example : -- a nested array value is rejected (`anyFlatNondet` only supports flat values)
  (Parser.run anyFlatNondet "{\"a\":[1,2]}").toOption == none
:= by native_decide

-- ---------------------------------------------------------------------------
-- E. Duplicate-key combinatorics.
-- ---------------------------------------------------------------------------

example : -- one duplicated key with two values yields both alternatives, in occurrence order
  keyValueAlts [("a", [Json.str "1", Json.str "2"])]
    == [[("a", Json.str "1")], [("a", Json.str "2")]]
:= by native_decide

example : -- two independently duplicated keys yield the full cross product of alternatives
  keyValueAlts [("a", [Json.str "1", Json.str "2"]), ("b", [Json.str "x", Json.str "y"])]
    == [ [("a", Json.str "1"), ("b", Json.str "x")]
       , [("a", Json.str "1"), ("b", Json.str "y")]
       , [("a", Json.str "2"), ("b", Json.str "x")]
       , [("a", Json.str "2"), ("b", Json.str "y")]
       ]
:= by native_decide

example : -- a duplicated key written two different ways (a literal `"a"` vs. the equivalent
          -- `\u0061` escape) is still recognized as one duplicated key, not two distinct keys
  (Parser.run anyFlatNondet "{\"a\":1,\"\\u0061\":2}").toOption.map List.length = some 2
:= by native_decide

example : -- two independently duplicated keys in the same object yield the full 4-way cross
          -- product at the parser level too
  (Parser.run anyFlatNondet "{\"a\":1,\"a\":2,\"b\":10,\"b\":20}").toOption.map List.length
    = some 4
:= by native_decide

example : -- a duplicated `email_verified` where one occurrence is valid and the other is not
          -- makes `payloads_from_json_string` reject the whole input: `mapM` requires *every*
          -- alternative implied by the duplicate keys to validate, not just one
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    jsonInput_duplicated_email_verified_conflict
  ).toOption
    == .none
:= by native_decide

example : -- same interaction as above, but with a duplicated `nonce` (one all-digits, one not)
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    jsonInput_duplicated_nonce_conflict
  ).toOption
    == .none
:= by native_decide

-- ---------------------------------------------------------------------------
-- F. `payload_from_json` field validation.
-- ---------------------------------------------------------------------------

example : -- missing `aud` field
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput_no_aud (emailVerified := "true"))
  ).toOption
    == .none
:= by native_decide

example : -- missing `sub` field, while `uidKey := .sub`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput_no_sub (emailVerified := "true"))
  ).toOption
    == .none
:= by native_decide

example : -- missing `email_verified` field
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    jsonInput_no_email_verified
  ).toOption
    == .none
:= by native_decide

example : -- missing `nonce` field
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput_no_nonce (emailVerified := "true"))
  ).toOption
    == .none
:= by native_decide

example : -- `iat` given as a non-integer JSON number
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput_bad_iat (emailVerified := "true"))
  ).toOption
    == .none
:= by native_decide

-- example : -- `exp` given as a JSON string instead of a number
--   (payloads_from_json_string
--     (uidKey := .sub)
--     (extraFieldKey := "shoe_size")
--     -- (expHorizon := 3602)
--     (jsonInput_string_exp (emailVerified := "true"))
--   ).toOption
--     == .none
-- := by native_decide

example : -- `email_verified` given as a JSON number, array, or null is rejected
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "0"))
  ).toOption
    == .none
  ∧ (payloads_from_json_string
      (uidKey := .sub)
      (extraFieldKey := "shoe_size")
      -- (expHorizon := 3602)
      (jsonInput (emailVerified := "[]"))
    ).toOption
    == .none
  ∧ (payloads_from_json_string
      (uidKey := .sub)
      (extraFieldKey := "shoe_size")
      -- (expHorizon := 3602)
      (jsonInput (emailVerified := "null"))
    ).toOption
    == .none
:= by native_decide

example : -- `email_verified` given as `"True"` (wrong case) is rejected: only `true`/`false`/
          -- `"true"`/`"false"` are accepted
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "True".quote))
  ).toOption
    == .none
:= by native_decide

-- example : -- `iat + expHorizon = exp` exactly (the boundary itself, not past it) is still rejected
--   (payloads_from_json_string
--     (uidKey := .sub)
--     (extraFieldKey := "shoe_size")
--     -- (expHorizon := 3601)
--     (jsonInput (emailVerified := "true"))
--   ).toOption
--     == .none
-- := by native_decide

example : -- uid key is `email`, and `email_verified` is `true`: succeeds
  (payloads_from_json_string
    (uidKey := .email)
    (extraFieldKey := "shoe_size")
    -- (expHorizon := 3602)
    (jsonInput (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy email",
          aud := "dummy aud",
          iat := 1719866138,
          -- exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

-- ---------------------------------------------------------------------------
-- G. `emailVerifiedFromJson`.
-- ---------------------------------------------------------------------------

example :
  (emailVerifiedFromJson (Json.bool true)).toOption = some true
  ∧ (emailVerifiedFromJson (Json.bool false)).toOption = some false
  ∧ (emailVerifiedFromJson (Json.str "true")).toOption = some true
  ∧ (emailVerifiedFromJson (Json.str "false")).toOption = some false
:= by native_decide

example :
  (emailVerifiedFromJson (Json.str "TRUE")).toOption = none
  ∧ (emailVerifiedFromJson (Json.str "")).toOption = none
  ∧ (emailVerifiedFromJson (Json.num 0)).toOption = none
  ∧ (emailVerifiedFromJson Json.null).toOption = none
  ∧ (emailVerifiedFromJson (Json.arr #[])).toOption = none
:= by native_decide

example : -- the local string lexer (`Parser.str`) agrees with `Json.parse` on `\n`/`\t`/`\uXXXX` escapes
  (Parser.run Parser.jsonFlatValue "\"a\\nb\\tc\\u0041\"").toOption.isSome
  ∧ (Parser.run Parser.jsonFlatValue "\"a\\nb\\tc\\u0041\"").toOption
      == (Lean.Json.parse "\"a\\nb\\tc\\u0041\"").toOption
:= by native_decide

example : -- the local number lexer (`Parser.ourNum`) agrees with `Json.parse` on a signed decimal with an exponent
  (Parser.run Parser.jsonFlatValue "-1.5e2").toOption.isSome
  ∧ (Parser.run Parser.jsonFlatValue "-1.5e2").toOption == (Lean.Json.parse "-1.5e2").toOption
:= by native_decide

end Keyless
