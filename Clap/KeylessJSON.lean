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
  exp            : ℕ
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

/--
Like `Json.Parser.anyCore`, but only parses flat JSON values (strings, numbers,
booleans, null), never arrays or objects. Since it never recurses into itself,
unlike `anyCore` it does not need to be `partial`.
-/
def jsonFlatValue : Parser Json := do
  let c ← peek!
  if c == '\"' then
    skip
    let s ← Json.Parser.str
    ws
    return Json.str s
  else if c == 'f' then
    skipString "false"; ws
    return Json.bool false
  else if c == 't' then
    skipString "true"; ws
    return Json.bool true
  else if c == 'n' then
    skipString "null"; ws
    return Json.null
  else if c == '-' || ('0' <= c && c <= '9') then
    let n ← Json.Parser.num
    ws
    return Json.num n
  else
    fail "unexpected input"

/--
Parse a list of one or more key-value pairs followed by a "}".
Implemented like `Json.Parser.objectCore`, but it keeps all the claims from the
top level that share the same key.
-/
def objectCoreAllPairs' (acc : Std.TreeMap.Raw String (List Json)) :
  Parser (Std.TreeMap.Raw String (List Json))
:= do
  Json.Parser.lookahead (fun c => c == '"') "\""; skip
  let k ← Json.Parser.str
  ws
  Json.Parser.lookahead (fun c => c == ':') ":"; skip; ws
  let v ← jsonFlatValue
  let c ← any
  if c == '}' then
    ws
    return acc.mergeWith (fun _ v₁ v₂ ↦ v₁ ++ v₂) {(k, [v])}
  else if c == ',' then
    ws
    objectCoreAllPairs' <| acc.mergeWith (fun _ v₁ v₂ ↦ v₁ ++ v₂) {(k, [v])}
  else
    fail "unexpected character in object"
  termination_by True
  decreasing_by sorry

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
  ws
  Json.Parser.lookahead (fun c => c == '{') "{"; skip; ws
  let c ← peek!
  if c == '}' then
    skip; ws
    pure [Json.obj ∅]
  else do
    let pairs ← objectCoreAllPairs' ∅
    let alts := keyValueAlts pairs.toList
    pure (alts.map (fun kvs => Json.obj (kvs.foldl (fun m (k, v) => m.insert k v) ∅)))

def payload_from_json
  (uidKey : UidKey)
  (expHorizon : ℕ)
  (extraFieldKey : String)
  (j : Json)
  :
  Except String AptosPayload
:= do
  let iss : String <- j.getObjValAs? String "iss"
  let aud : String <- j.getObjValAs? String "aud"
  let iat : ℕ <- j.getObjValAs? ℕ "iat"
  let exp : ℕ <- j.getObjValAs? ℕ "exp"
  let uid : String <- j.getObjValAs? String uidKey.fieldName
  let emailVerifiedJson : Json <- j.getObjVal? "email_verified"
  let email_verified : Bool <- emailVerifiedFromJson emailVerifiedJson
  let nonce : String <- j.getObjValAs? String "nonce"
  let extra_field : String <- j.getObjValAs? String extraFieldKey

  if !nonce.all Char.isDigit then
    -- Equal to Poseidon(epk, epk_len, exp_date, blinder)?
    throw s!"The field (nonce) must be a digit string, but ({nonce}) contains a non-digit character."

  -- TODO: These checks are not syntactic. Move them outside the parsing function?
  if uidKey == UidKey.email && email_verified = false then
    throw s!"The user id key is email, but email_verified is false"

  if iat + expHorizon ≤ exp then
    throw s!"iat + expHorizon ≤ exp ({iat} + {expHorizon} = {iat + expHorizon} ≤ {exp})"

  -- if exp ≤ iat then
  -- Aptos "We do not assert the expiration date is in the future (i.e., assert exp_date > jwt["iat"])""


  -- https://openid.net/specs/openid-connect-core-1_0.html#IDToken
  -- "current date/time MUST be before the expiration date/time listed in the value."
  -- what does aptos check?

  return { iss, aud, uid, iat, exp, email_verified, nonce, extra_field }

def payloads_from_json_string
  (uidKey : UidKey)
  (extraFieldKey : String)
  (expHorizon : ℕ)
  (s: String) :
  Except String (List AptosPayload)
:= do
  let j : List Json <- Parser.run anyFlatNondet s
  j.mapM (payload_from_json uidKey expHorizon extraFieldKey)

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


example : -- `email_verified` is the bool `true`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    (expHorizon := 3602)
    (jsonInput (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

example : -- duplicated `iss`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    (expHorizon := 3602)
    (jsonInput_duplicated_iss1 (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      , { iss := "dummy iss 2",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide


example : -- `email_verified` is the string `"true"`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    (expHorizon := 3602)
    (jsonInput (emailVerified := "true"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

example : -- `email_verified` is the bool `false`
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "shoe_size")
    (expHorizon := 3602)
    (jsonInput (emailVerified := "false"))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          exp := 1719869739,
          email_verified := false,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "40" }
      ]
:= by native_decide

example : -- user id key is `email`, but `email_verified` is `"false"`
  (payloads_from_json_string
    (uidKey := .email)
    (extraFieldKey := "shoe_size")
    (expHorizon := 3602)
    (jsonInput (emailVerified := "false".quote))
  ).toOption
    == .none
:= by native_decide

example : -- iat + expHorizon ≤ exp
  (payloads_from_json_string
    (uidKey := .email)
    (extraFieldKey := "shoe_size")
    (expHorizon := 1)
    (jsonInput (emailVerified := "true"))
  ).toOption
    = .none
  := by native_decide

example : -- extra field exists, it's "email"
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "email")
    (expHorizon := 6002)
    (jsonInput (emailVerified := "true".quote))
  ).toOption
    == some
      [ { iss := "dummy iss",
          uid := "dummy sub",
          aud := "dummy aud",
          iat := 1719866138,
          exp := 1719869739,
          email_verified := true,
          nonce := "159196287899032468733794277330513742183729069551015157917",
          extra_field := "dummy email" }
      ]
:= by native_decide

example : -- extra field doesn't exist
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "nonexistent")
    (expHorizon := 6002)
    (jsonInput (emailVerified := "true".quote))
  ).toOption
    = .none
  := by native_decide

example : -- missing iss field
  (payloads_from_json_string
    (uidKey := .sub)
    (extraFieldKey := "email")
    (expHorizon := 6002)
    (jsonInput_no_iss (emailVerified := "true"))
  ).toOption
    = none
  := by native_decide

-- example : -- with no duplicate keys, `anyFlatNondet` returns exactly one alternative
--   (Parser.run anyFlatNondet (jsonInput (emailVerified := "true"))).map List.length = .ok 1
--   := by native_decide

-- example : -- a duplicated `iss` field yields exactly the two alternatives implied by its
--           -- two occurrences, one per possible "winner"
--   ((Parser.run anyFlatNondet (jsonInput_duplicated_iss1 (emailVerified := "true"))).map
--     (fun alts =>
--       alts.length == 2 &&
--       alts.any (fun j => (j.getObjValAs? String "iss").toOption == some "dummy iss") &&
--       alts.any (fun j => (j.getObjValAs? String "iss").toOption == some "dummy iss 2")))
--     = .ok true
--   := by native_decide

end Keyless
