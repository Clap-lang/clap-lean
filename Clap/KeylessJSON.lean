import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

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

open Lean Json ToJson FromJson

namespace Keyless

#check Lean.Json.parse

/-

A value of `StringOrURI` type that contains a ":" character MUST be a URI, not a string
*TODO: Does Aptos check this?*

**iss**
  - of type `StringOrURI`, actually just a string

**aud**
  - of type `StringOrURI` (or array of `StringOrURI`s, but not for Aptos)

**uid_key** is The name of the key in the claim that maps to the user identifier; e.g., "sub" or "email"

**sub**
  - of type `StringOrURI`, actually just a string

AIP-061 gives `email` as an example of `extra_field`

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
  deriving Inhabited, Repr

/-- `email_verified` may be given as a JSON boolean (`true`/`false`) or as a JSON
string (`"true"`/`"false"`); any other value is rejected. -/
def emailVerifiedFromJson : Json → Except String Bool
  | .bool b     => return b
  | .str "true"  => return true
  | .str "false" => return false
  | .str s => throw s!"The field (email_verified) must be true, false, \"true\" or \"false\", but got (\"{s}\")."
  | _ => throw "The field (email_verified) must be a boolean or a string."

def payload_from_json_string
  (uidKey : UidKey)
  (extraFieldKey : String)
  (expHorizon : ℕ)
  (s: String) :
  Except String AptosPayload
:= do
  let j : Json <- Json.parse s

  let iss : String <- j.getObjValAs? String "iss"
  let aud : String <- j.getObjValAs? String "aud"
  let iat : ℕ <- j.getObjValAs? ℕ "iat"
  let exp : ℕ <- j.getObjValAs? ℕ "exp"
  let uid : String <- j.getObjValAs? String uidKey.fieldName
  let emailVerifiedJson : Json <- j.getObjVal? "email_verified"
  let email_verified : Bool <- emailVerifiedFromJson emailVerifiedJson
  let nonce : String <- j.getObjValAs? String "nonce"
  let extra_field : String <- j.getObjValAs? String extraFieldKey

  -- TODO: Move these checks outside the parsing function?
  -- if iss.contains ':' then
  --   throw s!"The field (iss) must be a string, but ({iss}) contains ':' which makes it an URI according to RFC-7512."
  -- if aud.contains ':' then
  --   throw s!"The field (aud) must be a string, but ({aud}) contains ':' which makes it an URI according to RFC-7512."
  if uidKey == UidKey.email && email_verified = false then
    throw s!"The user id key is email, but email_verified is false"
  if !nonce.all Char.isDigit then
    -- Equal to Poseidon(epk, epk_len, exp_date, blinder)?
    throw s!"The field (nonce) must be a digit string, but ({nonce}) contains a non-digit character."
  if iat + expHorizon > exp then
    throw s!"iat + expHorizon > exp ({iat} + {expHorizon} = {iat + expHorizon} ≤ {exp})"

  return { iss, aud, uid, iat, exp, email_verified, nonce, extra_field }

def String.quote s := "\"" ++ s ++ "\""
def claim (k v : String) := k.quote ++ " : " ++ v

def dummyNonce : String := "15919628789903246873379427733051374218372906955101515791742506401291192372556"

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
 where
  String.quote s := "\"" ++ s ++ "\""
  claim k v := k.quote ++ " : " ++ v

#check payload_from_json_string (uidKey := .sub) (extraFieldKey := "email") (expHorizon := 1) (jsonInput "true")
-- `email_verified` given as a JSON boolean
#eval payload_from_json_string (uidKey := .sub) (extraFieldKey := "email") (expHorizon := 1) (jsonInput "true")
#eval payload_from_json_string (uidKey := .email) (extraFieldKey := "email") (expHorizon := 1) (jsonInput "false")
-- `email_verified` given as a JSON string
#eval payload_from_json_string (uidKey := .sub) (extraFieldKey := "email") (expHorizon := 1) (jsonInput "true".quote)
#eval payload_from_json_string (uidKey := .sub) (extraFieldKey := "email") (expHorizon := 3602) (jsonInput "true".quote)
#eval payload_from_json_string (uidKey := .email) (extraFieldKey := "email") (expHorizon := 1) (jsonInput "false".quote)
-- `email_verified` given as an invalid string
#eval payload_from_json_string (uidKey := .sub) (extraFieldKey := "email") (expHorizon := 1) (jsonInput "yes".quote)

#eval payload_from_json_string (uidKey := .sub) (extraFieldKey := "shoe_size") (expHorizon := 1) (jsonInput "true".quote)

end Keyless
