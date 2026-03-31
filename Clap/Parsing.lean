import Lean
open Lean.Json

#check Lean.Json.getObj?
#check Lean.Json.getObjValD
#check Lean.Json.getObjValAs?

def verify : String → String → String → Option Unit := sorry

def parseKey (s k : String) : Except String String := do
  let json ← Lean.Json.parse s
  json.getObjValAs? String k

def sound (s k v : String) : Prop :=
  verify s k v = some () → parseKey s k = Except.ok v

inductive StateEscaped where
  | outsideQuotes
  | insideQuotes
  | escapeOutsideQuotes
  | escapeInsideQuotes
  | invalidJson

-- TODO should also escape \n and \t
def notEscaped (state : StateEscaped) (c : Char) : StateEscaped :=
  match state with
  | .outsideQuotes =>
    if c = '"' then .invalidJson
    else if c = '\\' then .escapeOutsideQuotes
    else .outsideQuotes
  | .insideQuotes =>
    if c = '"' then .invalidJson
    else if c = '\\' then .escapeInsideQuotes
    else .insideQuotes
  | .escapeOutsideQuotes =>
    if c = '"' then .insideQuotes
    else .invalidJson
  | .escapeInsideQuotes =>
    if c = '"' then .outsideQuotes
    else if c = '\\' then .insideQuotes
    else .invalidJson
  | .invalidJson => .invalidJson

-- context free, any state `some 1` is accepting
def nested (c : Char) (stackSize : Nat) : Option Nat :=
  match stackSize with
  | 0 =>
    if c = '{' then some 1
    else if c = '}' then none -- invalid json
    else some 0
  | 1 =>
    if c = '{' then some 2
    else if c = '}' then some 0
    else some 1
  | n =>
    if c = '{' then some (n+1)
    else if c = '}' then some (n-1)
    else some n


-- https://jsonlint.com/json-stringify

#eval Lean.Json.parse "\"a\\\\\""

def test := json% {
  nest : {mail : "bo\\b@mail.com"},
  mail : "alice@mail.com"
}

#eval s!"{test}"

-- #check Lean.Json.parse
-- def valid (s:String) : Prop :=
--    Except.isOk (Lean.Json.parse s)

-- def membership (sub:String) (s:String) : Prop :=
--   String.contains s sub

namespace Examples

/- In case of duplicate keys, the last one is kept -/

def duplicate := "{\"mail\": \"first@mail.com\", \"mail\": \"second@mail.com\"}"

/--
info: ok: {"mail": "second@mail.com"}
-/
#guard_msgs in
#eval Lean.Json.parse duplicate


/- a field could appear earlier but be nested in another field -/

def nested := json% {
  nest : {mail : "bob@mail.com"},
  mail : "alice@mail.com"
}

/--
info: "{\"nest\": {\"mail\": \"bob@mail.com\"}, \"mail\": \"alice@mail.com\"}"
-/
#guard_msgs in
#eval s!"{nested}"


/- Just a string, not nested enough. -/

def notObj := json% "bob@mail.com"

/--
info: "\"bob@mail.com\""
-/
#guard_msgs in
#eval s!"{notObj}"


/- A field could appear earlier but be inside a string.
   This case should not be possible if the json is valid.
-/

def escaped := json% {
  escape : "\"mail\": \"bob@mail.com\"",
  mail : "alice@mail.com"
}

/--
info: "{\"mail\": \"alice@mail.com\", \"escape\": \"\\\"mail\\\": \\\"bob@mail.com\\\"\"}"
-/
#guard_msgs in
#eval s!"{escaped}"

end Examples
