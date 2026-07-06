import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs

namespace Clap

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

inductive Wg (p : ℕ) : Type where
  | nil
  | cons (_ : ZMod p) (_ : Wg p)
  | input (_ : ZMod p → Wg p)

def Wg.repr (l : ℕ) (c : Wg p) : Std.Format :=
  letI go (l : ℕ) (k : (ZMod p) → Wg p) := repr (l+1) (k l)
  match c with
  | .nil => "[]"
  | .cons e c => s!"{_root_.repr e} :: {repr l c}"
  | .input k => s!"λ{l} {go l k}"

instance : Repr (Wg p) where
  reprPrec c _ := c.repr 0

instance : ToString (Wg p) :=
  ⟨Std.Format.pretty ∘ Wg.repr 0⟩

end Clap
