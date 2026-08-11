import Mathlib.Data.List.Basic

/-!
# A concrete-syntax model of JSON (RFC 8259)

This file specifies JSON *by reconstruction*. We assert that the string is exactly what you get
by re-serializing a structured tree.

```
Parses s d  ↔  DocWF d ∧ s = Doc.serialize d
```

For that equation to be usable, `serialize` must be a genuine inverse of parsing, so the tree is a
concrete-syntax tree. It carries the whitespace, the exact spelling of
numbers, and the raw (still-escaped) bodies of string literals. Nesting is modelled.

Specification only for now every theorem below is stated and left `sorry`.
-/

namespace Spec.Json

/-! ## Lexical

Defined on `List Char` and applied to `String.toList` because the tree is `String`-valued, but grammar
predicates needs structural induction (probably) -/

/-- RFC 8259 §2 `ws`: space, horizontal tab, line feed, carriage return. In
particular vertical tab and form feed are not JSON whitespace. -/
def IsWsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Every character of `s` is JSON whitespace. -/
def IsWs (s : String) : Prop :=
  ∀ c ∈ s.toList, IsWsChar c

def IsHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- RFC 8259 §7: the lowest code point allowed to appear unescaped in a string body. C0 control
characters (`< MinUnescapedCodepoint`, e.g. `\n`, `\t`, NUL) must instead go through `esc`/`escU`. -/
def MinUnescapedCodepoint : Nat := 0x20

/-- RFC 8259 §7: the characters between a string literal's delimiting quotes. Escapes are not expanded, so
the body is recoverable byte for byte.

this is what makes `Value.serialize` injective on strings. No unescaped `"` can
appear inside a body, so the closing quote is unambiguous, and since a `\` must itself begin a
legal escape, the backslash-parity that decides whether a `"` closes the literal is determined. -/
inductive StrBodyChars : List Char → Prop
  | nil : StrBodyChars []
  | lit {c : Char} {s : List Char} :
      c ≠ '"' → c ≠ '\\' → MinUnescapedCodepoint ≤ c.toNat → StrBodyChars s → StrBodyChars (c :: s)
  | esc {c : Char} {s : List Char} :
      c ∈ ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'] → StrBodyChars s →
      StrBodyChars ('\\' :: c :: s)
  | escU {a b c d : Char} {s : List Char} :
      IsHexDigit a → IsHexDigit b → IsHexDigit c → IsHexDigit d → StrBodyChars s →
      StrBodyChars ('\\' :: 'u' :: a :: b :: c :: d :: s)

/-- `s` is a legal string-literal body. -/
def IsStrBody (s : String) : Prop :=
  StrBodyChars s.toList

/-- RFC 8259 §6 `int`: `0`, or a nonzero digit followed by any digits. -/
def IsIntPart (s : List Char) : Prop :=
  s = ['0'] ∨ ∃ (d : Char) (ds : List Char),
    s = d :: ds ∧ '1' ≤ d ∧ d ≤ '9' ∧ ∀ c ∈ ds, c.isDigit

/-- RFC 8259 §6 `frac`: absent, or `.` followed by at least one digit. -/
def IsFracPart (s : List Char) : Prop :=
  s = [] ∨ ∃ ds : List Char, s = '.' :: ds ∧ ds ≠ [] ∧ ∀ c ∈ ds, c.isDigit

/-- RFC 8259 §6 `exp`: absent, or `e`/`E`, an optional sign, then at least one digit. -/
def IsExpPart (s : List Char) : Prop :=
  s = [] ∨ ∃ (e : Char) (sg ds : List Char),
    s = e :: (sg ++ ds) ∧ (e = 'e' ∨ e = 'E') ∧ (sg = [] ∨ sg = ['+'] ∨ sg = ['-'])
      ∧ ds ≠ [] ∧ ∀ c ∈ ds, c.isDigit

/-- RFC 8259 §6 `number = [minus] int [frac] [exp]`.

The full grammar is modelled, including `frac` and `exp`. -/
def IsNumLit (s : String) : Prop :=
  ∃ sign int frac exp : List Char,
    s.toList = sign ++ int ++ frac ++ exp
      ∧ (sign = [] ∨ sign = ['-'])
      ∧ IsIntPart int ∧ IsFracPart frac ∧ IsExpPart exp

/-! ## The tree -/

/-- The grammar's `element`: `ws value ws`. -/
structure Elem (α : Type) where
  wsL : String
  val : α
  wsR : String
deriving Repr, DecidableEq

/-- The grammar's `member`: `ws '"' key '"' ws ':' element`. -/
structure Memb (α : Type) where
  /-- Whitespace before the key's opening quote. -/
  wsL : String
  /-- Raw body of the key's string literal (escapes not expanded) -/
  key : String
  /-- Whitespace between the key's closing quote and the `:`. -/
  wsR : String
  val : Elem α
deriving Repr, DecidableEq

/-- A JSON value together with all of its concrete syntax.

`wsEmpty` on `arr`/`obj` is the whitespace of an empty collection (`{   }`); when the collection
is non-empty, leading whitespace belongs to the first element/member's `wsL` instead. Canonicity is
enforced by `ValueWF` -/
inductive Value where
  | null
  | bool (b : Bool)
  /-- The literal as written, e.g. `-1.50e+3`. -/
  | num (lit : String)
  /-- The raw, still-escaped body between the quotes. -/
  | str (body : String)
  | arr (wsEmpty : String) (elems : List (Elem Value))
  | obj (wsEmpty : String) (membs : List (Memb Value))
deriving Repr

/-! ## Serialization -/

mutual

/-- Render a value back to the exact text it came from. -/
def Value.serialize : Value → String
  | .null       => "null"
  | .bool true  => "true"
  | .bool false => "false"
  | .num lit    => lit
  | .str body   => "\"" ++ body ++ "\""
  | .arr ws es  => "[" ++ ws ++ Elems.serialize es
  | .obj ws ms  => "{" ++ ws ++ Membs.serialize ms

def Elem.serialize (e : Elem Value) : String :=
  e.wsL ++ Value.serialize e.val ++ e.wsR

def Memb.serialize (m : Memb Value) : String :=
  m.wsL ++ "\"" ++ m.key ++ "\"" ++ m.wsR ++ ":" ++ Elem.serialize m.val

/-- Members with their separators: each followed by `,`, the last by `}`.

Emitting the closing `}` from this function rather than from `Value.serialize`. It
makes every member's text end in `,` or `}`, so "a member together with its terminator" is a
contiguous slice of the object's text. -/
def Membs.serialize : List (Memb Value) → String
  | []      => "}"
  | [m]     => Memb.serialize m ++ "}"
  | m :: ms => Memb.serialize m ++ "," ++ Membs.serialize ms

def Elems.serialize : List (Elem Value) → String
  | []      => "]"
  | [e]     => Elem.serialize e ++ "]"
  | e :: es => Elem.serialize e ++ "," ++ Elems.serialize es

end

/-! ## Well-formedness

The inductive type alone admits nonsense: `.num "hello"`, or whitespace slots holding arbitrary
text. So membership in the grammar is a separate predicate.
-/

mutual

/-- **Canonicity** The `arr`/`obj` clauses require `wsEmpty = ""` whenever the collection
is non-empty. Without it `serialize` would not be injective (`.obj "x" [m]` and `.obj "y" [m]`
render identically, since `wsEmpty` is then absorbed by the first member's `wsL`), and
`Parses.unique` below would be false -/
inductive ValueWF : Value → Prop
  | null : ValueWF .null
  | bool (b : Bool) : ValueWF (.bool b)
  | num {lit : String} : IsNumLit lit → ValueWF (.num lit)
  | str {body : String} : IsStrBody body → ValueWF (.str body)
  | arr {ws : String} {es : List (Elem Value)} :
      IsWs ws → (es ≠ [] → ws = "") → ElemsWF es → ValueWF (.arr ws es)
  | obj {ws : String} {ms : List (Memb Value)} :
      IsWs ws → (ms ≠ [] → ws = "") → MembsWF ms → ValueWF (.obj ws ms)

inductive ElemWF : Elem Value → Prop
  | mk {a b : String} {v : Value} : IsWs a → ValueWF v → IsWs b → ElemWF ⟨a, v, b⟩

/-- A member is well-formed when its two whitespace slots really are whitespace, its key is a legal
string body, and its value element is well-formed. Note the key is checked as a raw body: the
escapes it may contain are not expanded (see `StrBodyChars`). -/
inductive MembWF : Memb Value → Prop
  | mk {a k b : String} {e : Elem Value} :
      IsWs a → IsStrBody k → IsWs b → ElemWF e → MembWF ⟨a, k, b, e⟩

inductive ElemsWF : List (Elem Value) → Prop
  | nil : ElemsWF []
  | cons {e : Elem Value} {es : List (Elem Value)} : ElemWF e → ElemsWF es → ElemsWF (e :: es)

inductive MembsWF : List (Memb Value) → Prop
  | nil : MembsWF []
  | cons {m : Memb Value} {ms : List (Memb Value)} : MembWF m → MembsWF ms → MembsWF (m :: ms)

end

/-! ## The specification proper -/

/-- RFC 8259 §2: `JSON-text = ws value ws`. -/
abbrev Doc := Elem Value

def Doc.serialize (d : Doc) : String :=
  Elem.serialize d

def DocWF (d : Doc) : Prop :=
  ElemWF d

/-- The JSON specification, in the reconstruction idiom: `s` is exactly the text of the
well-formed document `d`. -/
def Parses (s : String) (d : Doc) : Prop :=
  DocWF d ∧ s = Doc.serialize d

/-- `s` is well-formed JSON text. -/
def IsJson (s : String) : Prop :=
  ∃ d, Parses s d

/-- Serializing a well-formed tree lands back in the grammar. -/
theorem parses_serialize {d : Doc} (h : DocWF d) : Parses (Doc.serialize d) d := by
  sorry

/-- **The adequacy theorem.** The grammar is unambiguous, so a text determines its tree.

Everything downstream rests on this. Without it, `∃ d, s = serialize d` would be a weak claim -/
theorem Parses.unique {s : String} {d₁ d₂ : Doc} :
    Parses s d₁ → Parses s d₂ → d₁ = d₂ := by
  sorry

/-! ## Member access

Two readings of "the object has this member" are provided, because RFC 8259 leaves duplicate names
undefined and the two readings genuinely differ on such documents. See `HasUniqueMember`.
-/

def Value.membs? : Value → Option (List (Memb Value))
  | .obj _ ms => some ms
  | _         => none

/-- The weaker reading: some top-level member carries this key and value.

The raw key is compared, so a name written `"a"` and the same name
written `"a"` are distinct members here. RFC 8259 gives no canonical form for names, and
expanding escapes before comparing would be a different (also defensible) specification; this one
is chosen because it is what a byte-level reader sees. -/
def HasMember (v : Value) (key : String) (mv : Value) : Prop :=
  ∃ ms, v.membs? = some ms ∧ ∃ m ∈ ms, m.key = key ∧ m.val.val = mv

/-- The stronger reading: it is also the only member with that key.

RFC 8259 §4 says names SHOULD be unique but explicitly leaves the behaviour on duplicates
undefined, so on a document with two `"a"` members the two readings come apart: `HasMember` holds
of both values, `HasUniqueMember` of neither.

Uniqueness is counted over positions (via `List.filter`), so two byte-identical duplicate members
are correctly counted as two. -/
def HasUniqueMember (v : Value) (key : String) (mv : Value) : Prop :=
  ∃ ms, v.membs? = some ms
    ∧ (ms.filter (fun m => m.key == key)).length = 1
    ∧ ∃ m ∈ ms, m.key = key ∧ m.val.val = mv

/-- The document is well-formed and its root value is an object (rather than an array, string,
number, or literal).

RFC 8259 §2 allows any value at the root, so this is a genuine restriction. It is stated here
because "the root is an object" is the precondition of member access: `HasMember` is vacuously
unsatisfiable on a non-object root. Formats layered on JSON that require an object at the root —
RFC 7519's JWT Claims Set among them are expressed in terms of this. -/
def IsObjectDoc (d : Doc) : Prop :=
  DocWF d ∧ d.val.membs?.isSome

end Spec.Json

/-! ## Validation -/

namespace TestJson

open Spec.Json

/-- A representative object, with a decoy `"aud"` member buried one level down. -/
def sample : Doc :=
  ⟨"", .obj "" [⟨"",  "iss",    "", ⟨" ", .str "https://accounts.google.com", ""⟩⟩,
                ⟨" ", "aud",    "", ⟨" ", .str "client-id", ""⟩⟩,
                ⟨" ", "iat",    "", ⟨" ", .num "1700000000", ""⟩⟩,
                ⟨" ", "nested", "", ⟨" ", .obj "" [⟨"", "aud", "", ⟨"", .str "evil", ""⟩⟩], ""⟩⟩],
   ""⟩

/-- The tree reproduces the payload byte for byte — the reconstruction equation of `Parses`. -/
example : Doc.serialize sample =
    "{\"iss\": \"https://accounts.google.com\", \"aud\": \"client-id\", " ++
    "\"iat\": 1700000000, \"nested\": {\"aud\":\"evil\"}}" := by
  native_decide

/-- The real `aud` is a top-level member. -/
example : HasMember sample.val "aud" (.str "client-id") := by
  refine ⟨_, rfl, ?_⟩
  simp

/-- The nested decoy is not a top-level member -/
example : ¬ HasMember sample.val "aud" (.str "evil") := by
  rintro ⟨ms, hms, m, hm, hk, hv⟩
  simp [sample, Value.membs?] at hms
  subst hms
  simp at hm
  rcases hm with rfl | rfl | rfl | rfl <;> simp_all

/-- `ValueWF.obj` carries the canonicity clause `ms ≠ [] → ws = ""`. Leading whitespace could
otherwise be split between the object's own slot and the first member's, so one text would have two
trees and `Parses.unique` would be false. Only the second tree below is `ValueWF`. -/
example :
    Value.serialize (.obj " " [⟨"", "a", "", ⟨"", .num "1", ""⟩⟩])
      = Value.serialize (.obj "" [⟨" ", "a", "", ⟨"", .num "1", ""⟩⟩]) := by
  native_decide

end TestJson
