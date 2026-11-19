import Clap.Model.HashCons.Eval

namespace Clap

open HashConsM

inductive OhMyGodAnotherExpr (p n k : ℕ)
  | input (i : Fin n)
  | local (j : Fin k)
  | const (v : ZMod p)
  | binary_op (lhs rhs : OhMyGodAnotherExpr p n k) (op : BinaryOp)

namespace OhMyGodAnotherExpr

variable {p n k : ℕ}

section Syntax

scoped syntax:max (priority := high) &"input" term:max : term
scoped syntax:max (priority := high) &"local" term:max : term

scoped macro_rules
  | `(input $i) => `(OhMyGodAnotherExpr.input $i)
  | `(local $j) => `(OhMyGodAnotherExpr.local $j)

scoped instance (priority := high) : Add (OhMyGodAnotherExpr p n k) := ⟨(.binary_op · · .add)⟩
scoped instance (priority := high) : Sub (OhMyGodAnotherExpr p n k) := ⟨(.binary_op · · .sub)⟩
scoped instance (priority := high) : Mul (OhMyGodAnotherExpr p n k) := ⟨(.binary_op · · .mul)⟩
scoped instance (priority := high) {v : ℕ} : OfNat (OhMyGodAnotherExpr p n k) v := ⟨.const v⟩

variable {a b : OhMyGodAnotherExpr p n k}

@[grind _=_]
lemma add_eq_binary_op : a + b = .binary_op a b .add := rfl

@[grind _=_]
lemma sub_eq_binary_op : a - b = .binary_op a b .sub := rfl

@[grind _=_]
lemma mul_eq_binary_op : a * b = .binary_op a b .mul := rfl

@[grind _=_]
lemma ofNat_eq_const {v : ℕ} : (OfNat.ofNat v : OhMyGodAnotherExpr p n k) = .const (v : ZMod p) :=
  rfl

end Syntax

def _root_.Clap.BinaryOp.apply (op : BinaryOp) : ZMod p → ZMod p → ZMod p :=
  match op with
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

def eval (inputs : Vector (ZMod p) n) (locals : Vector (ZMod p) k) : OhMyGodAnotherExpr p n k → ZMod p
  | .input i              => inputs[i]
  | .local j              => locals[j]
  | .const v              => v
  | .binary_op lhs rhs op => op.apply (lhs.eval inputs locals) (rhs.eval inputs locals)

def toHashConsSt (inputs : Vector ExprRef n) (locals : Vector ExprRef k) :
  OhMyGodAnotherExpr p n k → HashConsM p (BoundRef p)
  | .input i => pure inputs[i]
  | .local j => pure locals[j]
  | .const v => mkConstant v
  | .binary_op lhs rhs op => do
    saveExpr
      (.binary_op (←lhs.toHashConsSt inputs locals) (←rhs.toHashConsSt inputs locals) op)

end OhMyGodAnotherExpr

def constraintsHold {p n k m : ℕ}
  (asm : Vector (OhMyGodAnotherExpr p n k) m)
  (inputs : Vector (ZMod p) n)
  (locals : Vector (ZMod p) k) : Prop := ∀ e ∈ asm, e.eval inputs locals = 0

/-
`isZero:`
  `numInputs      := 1`
  `numPrivate     := 1`
  `numPublic      := 1`
  `numConstraints := 2`

  `inputProp _ := True`

  - inv := local 0
  - x := input 0
  - out := local 1

  `constraints := #v[1 - inv * x - out, out * x]`
  `witness xs := (#v[xs[0]⁻¹], #v[if xs[0] = 0 then 1 else 0])`

Conditions on `p` are hypotheses of the spec's definition, e.g.
`def isZeroSpec (p : ℕ) [Fact p.Prime] : LawfulGateSpec p`.
-/

structure GateSpec (p : ℕ) where
  numInputs : ℕ
  numPrivate : ℕ -- Allocate this first
  numPublic : ℕ -- Allocate this last
  numConstraints : ℕ

  inputProp : Vector (ZMod p) numInputs → Prop

  constraints : Vector (OhMyGodAnotherExpr p numInputs (numPrivate + numPublic)) numConstraints
  witness : Vector (ZMod p) numInputs → Vector (ZMod p) numPrivate × Vector (ZMod p) numPublic

structure LawfulGateSpec (p : ℕ) extends GateSpec p where
  sound :
    ∀ (inputs : Vector (ZMod p) numInputs)
      (locals : Vector (ZMod p) numPrivate)
      (out : Vector (ZMod p) numPublic),
      constraintsHold constraints inputs (locals ++ out) →
      inputProp inputs ∧ out = (witness inputs).2

  complete :
    ∀ (inputs : Vector (ZMod p) numInputs),
      inputProp inputs →
      constraintsHold constraints inputs ((witness inputs).1 ++ (witness inputs).2)

namespace GateSpec

variable {p : ℕ}

abbrev numTotalVariables (spec : GateSpec p) : ℕ := spec.numPrivate + spec.numPublic

def assertions (spec : GateSpec p) (inputs : Vector (ZMod p) spec.numInputs) : Prop :=
  spec.inputProp inputs

def outputs (spec : GateSpec p)
            (inputs : Vector (ZMod p) spec.numInputs) : Vector (ZMod p) spec.numPublic :=
  (spec.witness inputs).2

def witnessInOrder (spec : GateSpec p) (inputs : Vector (ZMod p) spec.numInputs) :
  Vector (ZMod p) spec.numTotalVariables :=
  (spec.witness inputs).1 ++ (spec.witness inputs).2

end GateSpec

end Clap
