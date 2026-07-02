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

def random {var : Type} (a : Exp p var) : CircuitContM p var (FB p) := do
  eq0 (a - 42)
  return 4

def random' (var : Type) : CircuitContM p var Unit := do
  let x ← random 42
  eq0 x

def randomOption {var : Type} (a : Exp p var) : Option (FB p) := sorry

def eval {var} : Circuit p var → denotation var := sorry

example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
  (h : a = 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = eval ((pure 4 >>= c) fun _ ↦ .nil) := by
  sorry
  done

lemma CircuitContM.pure_def {var α} {x} :
  (pure x : CircuitContM p var α) = fun f ↦ f x := rfl

lemma CircuitContM.bind_def {var α} {x} {f : α → CircuitContM p var α} :
  bind (m := CircuitContM p var) x f = fun g => x fun i => f i g := rfl

open Classical in
example {var β : Type} {a : Exp p var} {c : FB p → Circuit p var}
  : 
  eval (random a c) =
  if a = 42
  then eval ((pure 4 : CircuitContM p var (FB p)) c)
  else .n := by
  rw [CircuitContM.pure_def]
  dsimp
  unfold random
  split_ifs with h
  rw [h]
  simp
  sorry

example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
  (h : a = 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = eval (c 4 fun _ ↦ .nil) := by
  sorry

example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
  (h : a ≠ 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = .n := by
  sorry

-- `if a = 42 then eval (c 4 fun _ ↦ .nil) else .n`

#eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random (p := TestPrime) (ZMod TestPrime) 5))
-- #eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random' (p := TestPrime) 5 (ZMod TestPrime)))

end EvalRandom

-- end
-- end LessThan

end Examples

end Clap
