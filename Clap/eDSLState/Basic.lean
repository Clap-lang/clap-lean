import Clap.Circuit

import Clap.eDSLState.Wheels

namespace Clap

namespace Circuit

section

def p : ℕ := 57

variable {var : Type}


def pretty [Repr var] [Index var] (c : Circuit p var) := repr 0 c

end

end Circuit

abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ
abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

def FixedExp.eval {p : ℕ} (varStore : ℕ → Option (ZMod p)) (x : FixedExp p) : Option (ZMod p) :=
  match x with
  | .c x => .some x
  | .v x => varStore x
  | .add l r => do (←eval varStore l) + (←eval varStore r)
  | .sub l r => do (←eval varStore l) - (←eval varStore r)
  | .mul l r => do (←eval varStore l) * (←eval varStore r)

inductive CircuitusPlanus (p : ℕ) where
  | nil
  | eq0 (e : FixedExp p)
  | lam (n : ℕ)
  | share (e : FixedExp p)
  | isZero (e : FixedExp p)
  | num2bits (w : ℕ) (e : FixedExp p)
  deriving Repr

abbrev Circuitus (p : ℕ) := Array (CircuitusPlanus p)

namespace Edsl

section

variable {p : ℕ}

structure CircuitState (p : ℕ) where
  numAlloc : ℕ
  circuit : Circuitus p
  deriving Repr

def CircuitState.init (p : ℕ) : CircuitState p := ⟨0, #[]⟩

abbrev CircuitStateM (p : ℕ) (α : Type) : Type := StateM (CircuitState p) α

def CircuitStateM.push {p : ℕ} (op : CircuitusPlanus p) : CircuitStateM p Unit := do
  let σ ← get
  set {σ with circuit := σ.circuit.push op}

def CircuitStateM.alloc {p : ℕ} : CircuitStateM p ℕ :=
  (·.1) <$> getModify fun σ ↦ {σ with numAlloc := σ.numAlloc + 1}

def CircuitStateM.run (α : Type) (m : CircuitStateM p α) : CircuitState p :=
  (·.2) <$> StateT.run m (CircuitState.init _)

section

variable {var : Type}

@[irreducible]
def eq0 (e : FixedExp p) : CircuitStateM p Unit := do
  CircuitStateM.push (.eq0 e)

@[irreducible]
def lam : CircuitStateM p ℕ := do
  CircuitStateM.alloc

@[irreducible]
def share (e : FixedExp p) : CircuitStateM p ℕ := do
  CircuitStateM.push (.share e)
  CircuitStateM.alloc

def testWithInput (x : ZMod 57) : CircuitStateM 57 Unit := do
  eq0 (.c x)
  let y ← share (.add 1 1)
  discard <| [1, 2, (.v y)].mapM eq0
  eq0 4

def test : CircuitStateM p Unit := do
  let x ← lam
  eq0 (.v x)
  let y ← share (.add 1 1)
  discard <| [1, 2, (.v y)].mapM eq0
  eq0 4

#eval test.run (p := 57)

-- Something like this?
-- Aaanyway... now I need to make sure to produce `.lam`s from initial arguments

end

end

end Edsl

-- @[irreducible]
-- def isZero (e : Exp p var) : CircuitContM p var var :=
--   Clap.Circuit.isZero e

-- @[irreducible]
-- def num2bits (w : ℕ) (e : Exp p var) : CircuitContM p var (List var) :=
--   Clap.Circuit.num2bits w e

-- end

-- end

-- end Edsl

-- namespace Examples

-- def TestPrime := 521

-- instance : Fact (Nat.Prime TestPrime) := ⟨by native_decide⟩

-- instance X : Circuit.Index (ZMod TestPrime) := ⟨fun x ↦ (x : ZMod _)⟩

-- open Lang Edsl

-- variable {p : ℕ}

-- namespace EvalRandom

-- def random {var : Type} (a : Exp p var) : CircuitContM p var (FB p) := do
--   eq0 (a - 42)
--   return 4

-- def random' (var : Type) : CircuitContM p var Unit := do
--   let x ← random 42
--   eq0 x

-- def randomOption {var : Type} (a : Exp p var) : Option (FB p) := sorry

-- def eval {var} : Circuit p var → denotation var := sorry

-- example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
--   (h : a = 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = eval ((pure 4 >>= c) fun _ ↦ .nil) := by
--   sorry
--   done

-- lemma CircuitContM.pure_def {var α} {x} :
--   (pure x : CircuitContM p var α) = fun f ↦ f x := rfl

-- lemma CircuitContM.bind_def {var α} {x} {f : α → CircuitContM p var α} :
--   bind (m := CircuitContM p var) x f = fun g => x fun i => f i g := rfl

-- open Classical in
-- example {var β : Type} {a : Exp p var} {c : FB p → Circuit p var}
--   :
--   eval (random a c) =
--   if a = 42
--   then eval ((pure 4 : CircuitContM p var (FB p)) c)
--   else .n := by
--   rw [CircuitContM.pure_def]
--   dsimp
--   unfold random
--   split_ifs with h
--   rw [h]
--   simp
--   repeat sorry

-- example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
--   (h : a = 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = eval (c 4 fun _ ↦ .nil) := by
--   sorry

-- example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
--   (h : a ≠ 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = .n := by
--   sorry

-- -- `if a = 42 then eval (c 4 fun _ ↦ .nil) else .n`

-- -- #eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random (p := TestPrime) (ZMod TestPrime) 5))
-- -- #eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random' (p := TestPrime) 5 (ZMod TestPrime)))

-- end EvalRandom

-- -- end
-- -- end LessThan

-- end Examples

end Clap
