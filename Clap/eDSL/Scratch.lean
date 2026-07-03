import Clap.eDSL.Specification

namespace Clap.Specification

def F (p: ℕ) (var: Type) : Type := Exp p var
def FB (p: ℕ) (var: Type) : Type := Exp p var
def F8 (p: ℕ) (var: Type) : Type := Exp p var

variable {p: ℕ} {var: Type}

namespace FB

def and (a b : FB p var) : FB p var := a.mul b

def or (a b : FB p var) : FB p var := (a.add b) - a.mul b

def not (a : FB p var) : FB p var := (Exp.c 1).sub a

end FB

namespace F

def eq (a b : F p var) : Edsl.CircuitContM p var (F p var) := do
  let v ← Edsl.isZero (a.sub b)
  pure (.v v)

def lessThan [Inhabited var] (w : ℕ) (a b : F p var) : Edsl.CircuitContM p var (FB p var) := do
  let d := (a.sub b) + (.c (2^w))
  let d ← Edsl.num2bits (w + 1) d
  return FB.not (.v d[w]!)

end F

namespace F8

def eq (a b : F8 p var) : Edsl.CircuitContM p var (FB p var) := F.eq a b

def lessThan [Inhabited var] (a b : F8 p var) : Edsl.CircuitContM p var (FB p var) :=
  F.lessThan 8 b a

def greaterThan [Inhabited var] (a b : F8 p var) : Edsl.CircuitContM p var (FB p var) :=
  lessThan b a

end F8

def isWhitespace [Inhabited var] (c : F8 p var) : Edsl.CircuitContM p var (FB p var) := do
  -- ASCII 9..13 are line break characters (tab, newline, vtab, ff, cr)
  let gt8 ← F8.greaterThan c (.c 8)
  let lt14 ← F8.lessThan c (.c 14)
  let isLineBreak : FB p var := gt8.and lt14
  let isSpace ← F8.eq c (.c 32) -- ASCII 32 is space
  pure (isLineBreak.or isSpace)

def isWhitespace_spec (c:Char) : Bool :=
  (c.toNat > 8 && c.toNat < 14) || c.toNat = 32

lemma isWhitespace_matches_spec [Inhabited var] (varStore : var → ZMod p) (c : F8 p var):
  Spec.matches_spec
    (varStore := varStore)
    (guard := True)
    (circuit := isWhitespace c)
    (result := FB.ofBool (isWhitespace_spec (F8.toChar c)))

end Clap.Specification
