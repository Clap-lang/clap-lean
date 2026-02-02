import Clap.Compilation
import Clap.Cfold
import R1serialize.Basic

namespace Clap

variable {p : ℕ} {var : Type} [Fact (Nat.Prime p)]

def Cs.toLevels (cs : Cs p Nat) (n:ℕ) : Cs p ℕ :=
  match cs with
  | .nil => .nil
  | .eq0 e cs => .eq0 e (cs.toLevels n)
  | .lam k => (k n).toLevels (n+1)

def toLevels (cs : Cs' p) : Cs p Nat := (cs ℕ).toLevels 1

def toR1CS (c : Circuit' p) : Cs p Nat :=
  let c := cfold' c
  let cs := toCs' c
  toLevels cs

/-
Linearity of an expression as defined at
https://docs.circom.io/circom-language/constraint-generation/

"Linear expression: an expression where only addition is used. It can also be
written using multiplication of variables by constants. For instance, the
expression `2*x + 3*y + 2` is allowed, as it is equivalent to
`x + x + y + y + y + 2`."
-/
def Exp.isLinear : Exp p ℕ → Bool
  | .v _ => true
  | .c _ => true
  | .add e₁ e₂ | .sub e₁ e₂ => e₁.isLinear && e₂.isLinear
  | .mul (.c _) (.v _) => true
  | .mul (.v _) (.c _) => true
  | .mul _ _ => false

/-- The sum of constants of a linear expression -/
def constantOfLinearExp : Exp p ℕ → ZMod p
  | .v _ => 0
  | .c constant => constant
  | .add e₁ e₂ => constantOfLinearExp e₁ + constantOfLinearExp e₂
  | .sub e₁ e₂ => constantOfLinearExp e₁ - constantOfLinearExp e₂
  | .mul _ _ => 0

def Exp.nVars₀ (i' : ℕ) : Exp p ℕ → ℕ
  | .v i => i ⊔ i'
  | .c _ => 0
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ => e₁.nVars₀ i' ⊔ e₂.nVars₀ i'

def Exp.nVars : Exp p ℕ → ℕ := Exp.nVars₀ 0

def Exp.toCoeff₀ (coeff : Array (ZMod p)) : Exp p ℕ → Array (ZMod p)
  | /- We should index variables by 1, so that `v 1` corresponds to wire 1
      and wire 0 is reserved for the constant.
    -/
    .v 0 => coeff
  | .v i =>
    let c := coeff[i]!
    coeff.set! i (c + 1)
  | .c _ => coeff
  | .add e₁ e₂ =>
    let coeff := e₁.toCoeff₀ coeff
    e₂.toCoeff₀ coeff
  | .sub e₁ e₂ =>
    let coeff := e₂.toCoeff₀ coeff |>.map (- ·)
    e₁.toCoeff₀ coeff
  | .mul (.c const) (.v i) | .mul (.v i) (.c const) =>
    let c := coeff[i]!
    coeff.set! i (c + const)
  | .mul _ _ => #[]

/- The coefficients of each variable in a linear expression -/
def Exp.toCoeff (e : Exp p ℕ) : Array (ZMod p) :=
  let nvar := e.nVars
  Exp.toCoeff₀ (Array.replicate (nvar + 1) 0) e
    |>.drop 1 -- Ignore `v 0`. (see `Exp.toCoeff₀`)

section Examples

open Exp

example : (1 + v 1 + 5 * v 3 + v 2 * 2 + 3 : Exp 7 ℕ).isLinear == true := by rfl
example : (v 5 * v 3 : Exp 7 ℕ).isLinear == false := by rfl
example : (v 1 * (1 + 1) : Exp 7 ℕ).isLinear == false := by rfl

example :
  (1 + v 1 + 5 * v 3 + v 2 * 2 + 3 : Exp 7 ℕ).toCoeff = #[1, 2, 5] := rfl
example /- not linear -/ : (v 5 * v 3 : Exp 7 ℕ).toCoeff = #[] := rfl
example /- not linear -/ : (v 1 * (1 + 1) : Exp 7 ℕ).toCoeff = #[] := rfl

example : (1 + 3 + 0 : Exp 7 ℕ).nVars = 0 := rfl
example : (1 + v 1 : Exp 7 ℕ).nVars = 1 := rfl
example : (1 + v 1 + v 5 : Exp 7 ℕ).nVars = 5 := rfl

end Examples

def Cs.nVars : Cs p ℕ → ℕ
  | .nil => 0
  | .eq0 (.sub (.mul a b) c) rest =>
    a.nVars ⊔ b.nVars ⊔ c.nVars ⊔ Cs.nVars rest
  | _ => 0

def quadraticToConstraints : Cs p ℕ → Constraints
  | .nil => #[]
  | .eq0 (.sub (.mul a b) c) rest =>
    if a.isLinear && b.isLinear && c.isLinear then
      let termsA := coefficientsToTerms (constantOfLinearExp a) a.toCoeff
      let termsB := coefficientsToTerms (constantOfLinearExp b) b.toCoeff
      let termsC := coefficientsToTerms (constantOfLinearExp c) c.toCoeff
      let constraint : Constraint :=
        { nA := ⟨termsA.size⟩
          nB := ⟨termsB.size⟩
          nC := ⟨termsC.size⟩
          termsA
          termsB
          termsC
        }
      #[constraint] ++ quadraticToConstraints rest
    else #[]
  | _ => #[]
 where
  coefficientsToTerms : ZMod p → Array (ZMod p) → Array (UInt32 × ℕ)
    | c₀, cs =>
      let head : UInt32 × ℕ := (0, c₀.val)
      let tail : Array (UInt32 × ℕ) :=
        (Array.range' 1 cs.size).zip cs |>.map fun (i, c) => (⟨i⟩, c.val)
      #[head] ++ tail |>.filter (·.snd != 0)

def quadraticToR1CS (cs : Cs p ℕ) : R1CSv1 :=
  let c := quadraticToConstraints cs
  let nVars := Cs.nVars cs
  let nWires := nVars + 1
  let h : Header := {
    fieldElemSize := ⟨fieldSize p⟩
    prime := p
    nWires := ⟨nWires⟩
    nPubOut := 0
    nPubIn := 0
    nPrvIn := ⟨nVars⟩
    nLabels := ⟨nWires⟩
    mConstraints := ⟨Array.size c⟩
  }
  let lm : WireToLabelMap := Array.range nWires |>.map UInt64.ofNat
  ⟨h, c, lm, (), ()⟩
 where
  /- Size in bytes of a field element. Must be a multiple of 8. -/
  fieldSize (p : ℕ) (size₀ : ℕ := 8) :=
    if p < 2^64 then size₀ else fieldSize (p >>> 64) (size₀ + 8)

private def cs₁ : Cs 7 Nat :=
  .eq0 (.v 1 * .v 2 - .c 3) .nil -- w₁ * w₂ - 3 * w₀ = 0

#guard quadraticToR1CS cs₁ ==
  { header :=
    { fieldElemSize := 8
      prime := 7
      nWires := 3
      nPubOut := 0
      nPubIn := 0
      nPrvIn := 2
      nLabels := 3
      mConstraints := 1
    }
    constraints :=
      #[{ nA := 1, nB := 1, nC := 1
          termsA := #[(1, 1)] -- w₁ * 1
          termsB := #[(2, 1)] -- w₂ * 1
          termsC := #[(0, 3)] -- w₀ * 3
        }
      ]
    wireToLabelMap := #[0, 1, 2]
    ultraPLONKCustomGateList := (), ultraPLONKCustomGateApplication := ()
  }


private def cs₂ : Cs 7 Nat :=
  .eq0 (.c 1 * .c 1 - .c 1) .nil

#guard quadraticToR1CS cs₂ ==
  { header :=
    { fieldElemSize := 8
      prime := 7
      nWires := 1
      nPubOut := 0
      nPubIn := 0
      nPrvIn := 0
      nLabels := 1
      mConstraints := 1
    }
    constraints :=
      #[{ nA := 1, nB := 1, nC := 1
          termsA := #[(0, 1)] -- w₀ * 1
          termsB := #[(0, 1)] -- w₀ * 1
          termsC := #[(0, 1)] -- w₀ * 1
        }
      ]
    wireToLabelMap := #[0]
    ultraPLONKCustomGateList := (), ultraPLONKCustomGateApplication := ()
  }

open Exp in
private def cs₃ : Cs 7 Nat :=
  .eq0 ((c 1 + 5 * v 1 + 2 * v 2) * (c 2 + v 1) - (v 2)) .nil

#guard quadraticToR1CS cs₃ ==
  { header :=
    { fieldElemSize := 8,
      prime := 7
      nWires := 3
      nPubOut := 0
      nPubIn := 0
      nPrvIn := 2
      nLabels := 3
      mConstraints := 1
    }
    constraints :=
      #[{ nA := 3, nB := 2, nC := 1
          termsA := #[(0, 1), (1, 5), (2, 2)] -- w₀ * 1 + w₁ * 5 + w₂ * 2
          termsB := #[(0, 2), (1, 1)] -- w₀ * 2 + w₁ * 1
          termsC := #[(2, 1)] -- w₂ * 1
        }
      ]
    wireToLabelMap := #[0, 1, 2]
    ultraPLONKCustomGateList := (), ultraPLONKCustomGateApplication := ()
  }

open Exp in
private def cs₄ : Cs 7 Nat :=
  .eq0 (v 1 * v 6 - v 4) <|
    .eq0 (v 1 * v 2 - v 4) <|
      .eq0 (v 1 * v 1 - v 1) .nil

#guard quadraticToR1CS cs₄ ==
  { header :=
    { fieldElemSize := 8
      prime := 7
      nWires := 7
      nPubOut := 0
      nPubIn := 0
      nPrvIn := 6
      nLabels := 7
      mConstraints := 3
    }
    constraints :=
      #[{ nA := 1, nB := 1, nC := 1
          termsA := #[(1, 1)] -- w₂ * 1
          termsB := #[(6, 1)] -- w₆ * 1
          termsC := #[(4, 1)] -- w₄ * 1
        },
        { nA := 1, nB := 1, nC := 1
          termsA := #[(1, 1)] -- w₁ * 1
          termsB := #[(2, 1)] -- w₂ * 1
          termsC := #[(4, 1)] -- w₄ * 1
        },
        { nA := 1, nB := 1, nC := 1
          termsA := #[(1, 1)] -- w₁ * 1
          termsB := #[(1, 1)] -- w₁ * 1
          termsC := #[(1, 1)] -- w₁ * 1
        }
      ]
    wireToLabelMap := #[0, 1, 2, 3, 4, 5, 6],
    ultraPLONKCustomGateList := (), ultraPLONKCustomGateApplication := () }

-- #eval serializeR1CS "cs1.r1cs" (quadraticToR1CS cs₁)
-- #eval serializeR1CS "cs2.r1cs" (quadraticToR1CS cs₂)
-- #eval serializeR1CS "cs3.r1cs" (quadraticToR1CS cs₃)
-- #eval serializeR1CS "cs4.r1cs" (quadraticToR1CS cs₄)

def r1csAble : Cs p ℕ -> Prop
  | .nil => True
  | .eq0 (.sub (.mul a b) c) rest =>
    a.isLinear ∧ b.isLinear ∧ c.isLinear ∧ r1csAble rest
  | _ => False
