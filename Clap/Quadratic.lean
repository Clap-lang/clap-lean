import Clap.Compilation
import Clap.Cfold
import R1Serialize.R1CS

namespace Clap

variable {p : ℕ} {var : Type} [Fact (Nat.Prime p)]

def Exp.scalarArithmetic₀ : Exp p var → Exp p var ⊕ ZMod p
  | .v var => .inl (.v var)
  | .c const => .inr const
  | .add l r =>
    match l.scalarArithmetic₀, r.scalarArithmetic₀ with
    | .inr c₁, .inr c₂ => .inr (c₁ + c₂)
    | .inr c₁, .inl e => .inl (.add (.c c₁) e)
    | .inl e, .inr c₂ => .inl (.add e (.c c₂))
    | .inl e₁, .inl e₂ => .inl (.add e₁ e₂)
  | .sub l r =>
    match l.scalarArithmetic₀, r.scalarArithmetic₀ with
    | .inr c₁, .inr c₂ => .inr (c₁ - c₂)
    | .inr c₁, .inl e => .inl (.sub (.c c₁) e)
    | .inl e, .inr c₂ => .inl (.sub e (.c c₂))
    | .inl e₁, .inl e₂ => .inl (.sub e₁ e₂)
  | .mul l r =>
    match l.scalarArithmetic₀, r.scalarArithmetic₀ with
    | .inr c₁, .inr c₂ => .inr (c₁ * c₂)
    | .inr c₁, .inl e => .inl (.mul (.c c₁) e)
    | .inl e, .inr c₂ => .inl (.mul e (.c c₂))
    | .inl e₁, .inl e₂ => .inl (.mul e₁ e₂)

def Exp.scalarArithmetic (e : Exp p var) : Exp p var :=
  match e.scalarArithmetic₀ with
  | .inl e => e
  | .inr const => .c const

section TestScalarArithmetic

open Exp

#guard
  ((4 * 3 - 5 * 2) * v 1 + (1 - (1 + 1)) * v 2 : Exp 7 ℕ).scalarArithmetic =
    ((2 * v 1) + (6 * v 2) : Exp 7 ℕ)

#guard
  ((5 * v 1 + (3 + 2) * v 2) * ((1 + 1) * v 1) : Exp 7 ℕ).scalarArithmetic =
    ((5 * v 1) + (5 * v 2)) * (2 * v 1)

#guard
  ((2 * (1 + ((2 * 1 + 1 * 2) * 2) + 1) * v 1) : Exp 7 ℕ).scalarArithmetic =
    20 * v 1

end TestScalarArithmetic

/-- Push constant multiplicatin until each constant is multiplied with a variable.
  To be used after `coeffArithmetic`.
-/
def Exp.mulByConstants : Exp p var → Exp p var
  | .v var => .v var
  | .c const => .c const
  | .add l r => .add l.mulByConstants r.mulByConstants
  | .sub l r => .sub l.mulByConstants r.mulByConstants
  | .mul l r =>
    match l, r with
    | .c const', .add l' r'
    | .add l' r', .c const' =>
      .add
        (mulByConstants <| .mul (.c const') l')
        (mulByConstants <| .mul (.c const') r')
    | .c const', .sub l' r'
    | .sub l' r', .c const' =>
      .sub
        (mulByConstants <| .mul (.c const') l')
        (mulByConstants <| .mul (.c const') r')
    | .c const', .mul l' r'
    | .mul l' r', .c const' =>
      -- Push the constant inside the left term of the multiplication.
      match mulByConstants (.mul (.c const') l') with
      | .c constₗ => mulByConstants <| .mul (.c constₗ) r'
      | l'' =>
        match mulByConstants r' with
        | .c constᵣ => mulByConstants <| .mul (.c (const' * constᵣ)) l'
        | r'' => .mul l'' r''
    | .c const₁, .c const₂ => .c (const₁ * const₂)
    | l, r => .mul l.mulByConstants r.mulByConstants

section TestMulByConstants

open Exp

#guard (3 * (v 1 * 2) : Exp 7 ℕ).mulByConstants = 6 * v 1

#guard (2 * (3 * v 1) : Exp 7 ℕ).mulByConstants = 6 * v 1

#guard
  (4 * v 1 * 2 + 2 * v 2 * 4 : Exp 7 ℕ).mulByConstants = 8 * v 1 + 8 * v 2

#guard
  (2 * (v 1 * 5) + 5 * (v 2 * 2) : Exp 7 ℕ).mulByConstants = 10 * v 1 + 10 * v 2

#guard
  (2 * (3 * v 1 + 1 * v 2) * 2 : Exp 7 ℕ).mulByConstants = 12 * v 1 + 4 * v 2

#guard
  (2 * (3 * v 1 * (v 2 * 4)) : Exp 7 ℕ).mulByConstants = (6 * v 1) * (v 2 * 4)

end TestMulByConstants

/-- Repesents the expression (A * B - C) -/
structure NormalQuadratic (p : ℕ) (var : Type) where
  A : Exp p var
  B : Exp p var
  C : Exp p var
  deriving Repr

/- To be used after `mulByConstants`. -/
def Exp.normalQuadratic₀ : Exp p var → Option (Exp p var ⊕ NormalQuadratic p var)
  | .v var => return .inl (.v var)
  | .c const => return .inl (.c const)
  | .add l r =>
    match l.normalQuadratic₀, r.normalQuadratic₀ with
    | some (.inl e₁), some (.inl e₂) => return .inl (.add e₁ e₂)
    | some (.inl e), some (.inr ⟨A, B, C⟩)
    | some (.inr ⟨A, B, C⟩), some (.inl e) =>
      -- e + (A * B - C) = A * B - (C - e)
      return .inr ⟨A, B, .sub C e⟩
    | _, _ => none
  | .sub l r =>
    match l.normalQuadratic₀, r.normalQuadratic₀ with
    | some (.inl e₁), some (.inl e₂) => return .inl (.sub e₁ e₂)
    | some (.inl e), some (.inr ⟨A, B, C⟩) =>
      -- e - (A * B - C) = (- A) * B - (C + e)
      return .inr ⟨.sub 0 A, B, .add C e⟩
    | some (.inr ⟨A, B, C⟩), some (.inl e₁) =>
      -- (A * B - C) - e₁ -> A * B - (C + e₁)
      return .inr ⟨A, B, .add C e₁⟩
    | _, _ => none
  | .mul l r =>
    match l.normalQuadratic₀, r.normalQuadratic₀ with
    | some (.inl e₁@(.c _)), some (.inl e₂@(.v _))
    | some (.inl e₁@(.v _)),   some (.inl e₂@(.c _)) =>
      return .inl (.mul e₁ e₂)
    | some (.inl e₁), some (.inl e₂) => return .inr ⟨e₁, e₂, .c 0⟩
    | _, _ => none

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

section

open Exp

#guard (1 + v 1 + 5 * v 3 + v 2 * 2 + 3 : Exp 7 ℕ).isLinear = true
#guard (v 5 * v 3 : Exp 7 ℕ).isLinear = false
#guard (v 1 * (1 + 1) : Exp 7 ℕ).isLinear == false

#guard (1 + v 1 + 5 * v 3 + v 2 * 2 + 3 : Exp 7 ℕ).toCoeff = #[1, 2, 5]
#guard
  (1 + v 1 - (3 * v 2) + 5 * v 3 + v 2 * 2 + 3 : Exp 7 ℕ).toCoeff = #[1, -1, 5]
#guard /- not linear -/ (v 5 * v 3 : Exp 7 ℕ).toCoeff = #[]
#guard /- not linear -/ (v 1 * (1 + 1) : Exp 7 ℕ).toCoeff = #[]

#guard (1 + 3 + 0 : Exp 7 ℕ).nVars = 0
#guard (1 + v 1 : Exp 7 ℕ).nVars = 1
#guard (1 + v 1 + v 5 : Exp 7 ℕ).nVars = 5

end

def Cs.nVars : Cs p ℕ → ℕ
  | .nil => 0
  | .eq0 (.sub (.mul a b) c) rest =>
    a.nVars ⊔ b.nVars ⊔ c.nVars ⊔ Cs.nVars rest
  | _ => 0

def quadraticToConstraints : Cs p ℕ → Constraints
  | .nil => #[]
  | .eq0 (.sub (.mul a b) c) rest =>
    if a.isLinear && b.isLinear && c.isLinear then
      #[constraint a b c] ++ quadraticToConstraints rest
    else #[]
  | _ => #[]
 where
  constraint (a b c : Exp p ℕ) : Constraint :=
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
    constraint
  coefficientsToTerms : ZMod p → Array (ZMod p) → Array (UInt32 × ℕ)
    | c₀, cs =>
      let head : UInt32 × ℕ := (0, c₀.val)
      let tail : Array (UInt32 × ℕ) :=
        (Array.range' 1 cs.size).zip cs |>.map fun (i, c) => (⟨i⟩, c.val)
      #[head] ++ tail |>.filter (·.snd != 0)

/--
  Tries bringing an expression to the standard R1CS form (A * B - C).
-/
def Exp.normalQuadratic (e : Exp p var) : Exp p var :=
  match e.scalarArithmetic.mulByConstants.normalQuadratic₀ with
  | none => e
  | some (.inl e) => .sub (.mul (.c 0) (.c 0)) (.sub 0 e)
  | some (.inr ⟨A, B, C⟩) => .sub (.mul A B) C

section TestConstraint

open Exp

private def Exp.r1csTransform (e : Exp p ℕ) : Option Constraint := do
  let r ← e.scalarArithmetic.mulByConstants.normalQuadratic₀
  match r with
  | .inl e => pure (quadraticToConstraints.constraint (.c 0) (.c 0) (.sub 0 e))
  | .inr ⟨A, B, C⟩ => pure (quadraticToConstraints.constraint A B C)

#guard
  (1 : Exp 7 ℕ).r1csTransform ==
  some
    { nA := 0, nB := 0, nC := 1
      termsA := #[]
      termsB := #[]
      termsC := #[(0, 6)] -- v 0 * (-1)
    }

#guard
  (2 * (2 * v 1 * 2) : Exp 7 ℕ).r1csTransform ==
  some
    { nA := 0, nB := 0, nC := 1
      termsA := #[]
      termsB := #[]
      termsC := #[(1, 6)] -- v 1 * (-1)
    }

#guard (v 1 + v 1 * v 2 - 1 + 3 * v 2 : Exp 7 ℕ).r1csTransform ==
  some
    { nA := 1, nB := 1, nC := 3
      termsA := #[(1, 1)]
      termsB := #[(2, 1)]
      termsC := #[(0, 1), (1, 6), (2, 3)]
      -- C = 1 + v 1 * (-1) + v 2 * (-3)
    }

#guard
  r1csTransform
    ((v 1 + 1 * (v 1 + (v 2 + v 3) * 2) * (2 * v 2 + 2 * v 1)) : Exp 7 ℕ)
    ==
    some
      { nA := 3, nB := 2, nC := 1,
        termsA := #[(1, 1), (2, 2), (3, 2)] -- A = v 1 + v 2 * 2 + v 3 * 2
        termsB := #[(1, 2), (2, 2)] -- B = v 1 * 2 + v 2 * 2
        termsC := #[(1, 6)] -- C = -1
      }


end TestConstraint

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

open Exp in
private def cs₅ : Cs 7 Nat :=
  .eq0 (1 + v 1 * 1).normalQuadratic <|
    .eq0 (2 * (v 1 + v 2) * (2 + 1) * (v 2 + (1 + 1)) + v 1).normalQuadratic <|
      .eq0 (v 1 * v 1).normalQuadratic .nil

#guard quadraticToR1CS cs₅ ==
  { header :=
      { fieldElemSize := 8,
        prime := 7,
        nWires := 3,
        nPubOut := 0,
        nPubIn := 0,
        nPrvIn := 2,
        nLabels := 3,
        mConstraints := 3
      },
    constraints :=
      #[{ nA := 0, nB := 0, nC := 2
          termsA := #[]
          termsB := #[]
          termsC := #[(0, 6), (1, 6)]
        },
        { nA := 2, nB := 2, nC := 1,
          termsA := #[(1, 6), (2, 6)],
          termsB := #[(0, 2), (2, 1)],
          termsC := #[(1, 6)]
        },
        { nA := 1, nB := 1, nC := 0
          termsA := #[(1, 1)]
          termsB := #[(1, 1)]
          termsC := #[]
        }
      ]
    wireToLabelMap := #[0, 1, 2]
    ultraPLONKCustomGateList := (), ultraPLONKCustomGateApplication := ()
  }

-- #eval serializeR1CS "cs1.r1cs" (quadraticToR1CS cs₁)
-- #eval serializeR1CS "cs2.r1cs" (quadraticToR1CS cs₂)
-- #eval serializeR1CS "cs3.r1cs" (quadraticToR1CS cs₃)
-- #eval serializeR1CS "cs4.r1cs" (quadraticToR1CS cs₄)

def r1csAble : Cs p ℕ -> Prop
  | .nil => True
  | .eq0 (.sub (.mul a b) c) rest =>
    a.isLinear ∧ b.isLinear ∧ c.isLinear ∧ r1csAble rest
  | _ => False
