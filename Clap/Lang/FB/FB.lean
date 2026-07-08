import Clap.Lang.F.F

namespace Clap.Lang

abbrev FB p := F p

namespace FB

def true (p : ℕ) [Fact (p ≥ 2)] : FB p := .c 1
def false (p : ℕ) [Fact (p ≥ 2)] : FB p := .c 0

variable {p : ℕ} [Fact (p ≥ 2)]

def isValid (x : FB p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1

def isAlwaysValid (x : FB p) : Prop :=
  ∀ varStore, x.isValid varStore

def toBool (x : FB p) (varStore : ℕ → Option (ZMod p)) : Bool :=
  x.eval varStore == .some 1

def ofBool (p : ℕ) [Fact (p ≥ 2)] (x : Bool) : FB p :=
  if x then FB.true p else FB.false p

lemma isValid_ofBool (b:Bool) : isAlwaysValid (FB.ofBool p b) := by
  unfold isAlwaysValid isValid FB.ofBool
  aesop

def matchesUnaryFunction (p : ℕ) [Fact (p ≥ 2)] (spec_function: Bool → Bool) (function : FB p → FB p) : Prop :=
  ∀ (a: FB p) varStore, a.isValid varStore →
    (function a).eval varStore =
    (FB.ofBool p (spec_function (a.toBool varStore))).eval varStore

-- def matchesConstraints (p : ℕ) [Fact (p ≥ 2)] (constraints: Prop) (function : Edsl.CircuitStateM p Unit) : Prop :=


end FB

end Clap.Lang
