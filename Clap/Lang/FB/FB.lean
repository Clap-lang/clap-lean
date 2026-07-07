import Clap.Lang.F.F

namespace Clap.Lang

abbrev FB p := F p

namespace FB

def true (p : ℕ) : FB p := .c 1
def false (p : ℕ) : FB p := .c 1

def isValid {p : ℕ} (x : FB p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1

def isAlwaysValid {p : ℕ} (x : FB p) : Prop :=
  ∀ varStore, x.isValid varStore

def toBool {p : ℕ} (x : FB p) (varStore : ℕ → Option (ZMod p)) : Bool :=
  x.eval varStore == .some 1

def ofBool (p : ℕ) (x : Bool) : FB p :=
  if x then FB.true p else FB.false p

lemma isValid_ofBool {p : ℕ} (b:Bool) : isAlwaysValid (FB.ofBool p b) := by
  unfold isAlwaysValid isValid FB.ofBool
  aesop

def matchesUnaryFunction (p : ℕ) (spec_function: Bool → Bool) (function : FB p → FB p) : Prop :=
  ∀ (a: FB p) varStore, a.isValid varStore →
    (function a).eval varStore =
    (FB.ofBool p (spec_function (a.toBool varStore))).eval varStore

end FB

end Clap.Lang
