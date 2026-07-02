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

section

variable {var : Type}

@[irreducible]
def eq0 (e : Exp p var) : CircuitContM p var Unit := fun c ↦
  Clap.Circuit.eq0 e (c ())

@[irreducible]
def lam : CircuitContM p var var :=
  Clap.Circuit.lam 

@[irreducible]
def share (e : Exp p var) : CircuitContM p var var :=
  Clap.Circuit.share e

@[irreducible]
def isZero (e : Exp p var) : CircuitContM p var var :=
  Clap.Circuit.isZero e

@[irreducible]
def num2bits (w : ℕ) (e : Exp p var) : CircuitContM p var (List var) :=
  Clap.Circuit.num2bits w e

end

end

end Edsl

namespace Examples

def TestPrime := 521

instance : Fact (Nat.Prime TestPrime) := ⟨by native_decide⟩

instance X : Circuit.Index (ZMod TestPrime) := ⟨fun x ↦ (x : ZMod _)⟩

open Lang Edsl

variable {p : ℕ}

namespace EvalRandom

def random (a : FB p) (var : Type) : CircuitContM p var (FB p) := do
  let a ← share a
  let b : Exp p (Exp p var) := Exp.v (Exp.v (p := p) a + Exp.v (p := p) a)
  return 4

def random' (var : Type) : CircuitContM p var Unit := do
  let x ← random 42 var
  eq0 x



#eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random (p := TestPrime) 5 (ZMod TestPrime)))

end EvalRandom

-- end
-- end LessThan

end Examples

end Clap
