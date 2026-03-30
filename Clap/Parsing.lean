import Lean
open Lean.Json

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
