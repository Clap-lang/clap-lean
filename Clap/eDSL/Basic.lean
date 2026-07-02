import Clap.Circuit
import Clap.Lang
import Mathlib.Control.Monad.Cont

namespace Clap

namespace Circuit

section

variable {var : Type} {p : ℕ}

def pretty [Repr var] [Index var] (c : Circuit p var) := repr 0 c

end

end Circuit

namespace Edsl

section

variable {p : ℕ}

abbrev CircuitContM (p : ℕ) (var : Type) (α : Type) : Type := Cont (Circuit p var) α

def CircuitContM.run (α var : Type) (m : CircuitContM p var α) : Circuit p var :=
  ContT.run m fun _ ↦ .nil

@[irreducible]
def eq0 {var : Type} (e : Exp p var) : CircuitContM p var Unit := fun c ↦
  Clap.Circuit.eq0 e (c ())

-- @[irreducible]
-- def lam : CircuitContM p (ZMod p) :=
--   Clap.Circuit.lam

-- @[irreducible]
-- def share (e : Expₑ p) : CircuitContM p (ZMod p) :=
--   Clap.Circuit.share e

-- @[irreducible]
-- def isZero (e : ZMod p) : CircuitContM p (ZMod p) :=
--   Clap.Circuit.isZero (.c e)

-- @[irreducible]
-- def num2bits (w : ℕ) (e : ZMod p) : CircuitContM p (List (ZMod p)) :=
--   Clap.Circuit.num2bits w (.c e)

end

end Edsl

-- namespace Examples

-- def TestPrime := 521

-- instance : Fact (Nat.Prime TestPrime) := ⟨by native_decide⟩

-- instance : Circuit.Index (ZMod TestPrime) := ⟨fun x ↦ (x : ZMod _)⟩

-- section

-- open Lang Edsl

-- variable {p : ℕ} {α β : Type}

-- namespace EvalRandom

-- def random (a : FB p) (var : Type) : CircuitContM p var (FB p) := do
--   let a ← eq0 a
--   let a ← eq0 1
--   return 4

-- end
-- end LessThan

-- end Examples

end Clap
