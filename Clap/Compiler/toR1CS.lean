import Clap.Model.ConstraintSystem.toCs
import R1Serialize.R1CS

namespace Clap

namespace ConstraintSystem

open HashConsM

/-- `A * B - C` -/
structure NormalQuadratic (p : ℕ) where
  A : BoundRef p
  B : BoundRef p
  C : BoundRef p
deriving BEq

variable {p : ℕ}

abbrev MemoM (p : ℕ) (α : Type) := StateT (Std.HashMap (BoundRef p) α) (HashConsM p)

def scalarArithmetic₀ (e : BoundRef p) : MemoM p (BoundRef p ⊕ ZMod p) (BoundRef p ⊕ ZMod p) := do
  if let some res := (← get)[e]? then return res
  let σ ← getThe (HashConsSt p)
  let res ←
    match _ : σ[e]? with
    | none
    | some (.v _) => pure (.inl e)
    | some (.c const) => pure (.inr const)
    | some (.binary_op l r op) => do
      match ← scalarArithmetic₀ l, ← scalarArithmetic₀ r with
      | .inr c₁, .inr c₂ =>
        let f : ZMod p → ZMod p → ZMod p :=
          match op with
          | .add => (· + ·)
          | .sub => (· - ·)
          | .mul => (· * ·)
        pure (.inr (f c₁ c₂))
      | .inr c₁, .inl e₂ => .inl <$> saveExpr (p := p) (.binary_op (←mkConstant c₁) e₂ op)
      | .inl e₁, .inr c₂ => .inl <$> saveExpr (p := p) (.binary_op e₁ (←mkConstant c₂) op)
      | .inl e₁, .inl e₂ => .inl <$> saveExpr (p := p) (.binary_op e₁ e₂ op)
  modify (·.insert e res)
  return res
termination_by e
decreasing_by
  all_goals
    have h_lt : e < σ.exprs.size := by
      by_contra h_ge
      simp_all
    have := σ.wellFormed e h_lt
    simp_all [CacheExpr.wellFormed]

def scalarArithmetic (e : BoundRef p) : MemoM p (BoundRef p ⊕ ZMod p) (BoundRef p) := do
  match ← scalarArithmetic₀ e with
  | .inl e => pure e
  | .inr const => mkConstant const

partial def mulByConstants (e : BoundRef p) : MemoM p (BoundRef p) (BoundRef p) := do
  if let some res := (← get)[e]? then return res
  let res ←
    match ← deref e with
    -- `.add l r`
    | some (.binary_op l r .add) => do (←mulByConstants l) + (←mulByConstants r)
    -- `.sub l r`
    | some (.binary_op l r .sub) => do (←mulByConstants l) - (←mulByConstants r)
    -- `.mul l r`
    | some (.binary_op l r .mul) =>
      match ← deref l, ← deref r with
      -- `.c const', .add l' r'`
      | some (.c const'), some (.binary_op l' r' .add)
      -- `.add l' r', .c const'`
      | some (.binary_op l' r' .add), some (.c const') => do
        (←mulByConstants (←((←mkConstant const') * l'))) +
          (←mulByConstants (←((←mkConstant const') * r')))
      -- `.c const', .sub l' r'`
      | some (.c const'), some (.binary_op l' r' .sub)
      -- `.sub l' r', .c const'`
      | some (.binary_op l' r' .sub), some (.c const') => do
        (←mulByConstants (←((←mkConstant const') * l'))) -
          (←mulByConstants (←((←mkConstant const') * r')))
      -- `.c const', .mul l' r'`
      | some (.c const'), some (.binary_op l' r' .mul)
      -- `.mul l' r', .c const'`
      | some (.binary_op l' r' .mul), some (.c const') => do
        let l'' ← mulByConstants (←((←mkConstant const') * l'))
        match ← deref l'' with
        -- `.c constₗ`
        | some (.c constₗ) => mulByConstants (←((←mkConstant constₗ) * r'))
        | _ =>
          let r'' ← mulByConstants r'
          match ← deref r'' with
          -- `.c constᵣ`
          | some (.c constᵣ) => mulByConstants (←((←mkConstant (const' * constᵣ)) * l'))
          | _ => l'' * r''
      -- `.c const₁, .c const₂`
      | some (.c const₁), some (.c const₂) => mkConstant (const₁ * const₂)
      -- `l, r`
      | _, _ => do (←mulByConstants l) * (←mulByConstants r)
      -- `.v` and `.c`
    | _ => pure e
  modify (·.insert e res)
  return res
where
  deref (e : BoundRef p) : MemoM p (BoundRef p) (Option (CacheExpr p)) :=
    return (←getThe (HashConsSt p))[e]?

def normalQuadratic₀ (e : BoundRef p) :
  MemoM p (Option (BoundRef p ⊕ NormalQuadratic p)) (Option (BoundRef p ⊕ NormalQuadratic p)) := do
  if let some res := (← get)[e]? then return res
  let σ ← getThe (HashConsSt p)
  let res ←
    match _ : σ[e]? with
    | none => pure none
    -- `.v` and `.c`
    | some (.v _)
    | some (.c _) => pure (some (.inl e))
    -- `.add l r`
    | some (.binary_op l r .add) => do
      match ← normalQuadratic₀ l, ← normalQuadratic₀ r with
      -- `some (.inl e₁), some (.inl e₂)`
      | some (.inl e₁), some (.inl e₂) => pure (some (.inl (←(e₁ + e₂))))
      -- `some (.inl e), some (.inr ⟨A, B, C⟩)`
      | some (.inl e'), some (.inr ⟨A, B, C⟩)
      -- `some (.inr ⟨A, B, C⟩), some (.inl e)`
      | some (.inr ⟨A, B, C⟩), some (.inl e') =>
        -- e + (A * B - C) = A * B - (C - e)
        pure (some (.inr ⟨A, B, (←(C - e'))⟩))
      -- `_, _`
      | _, _ => pure none
    -- `.sub l r`
    | some (.binary_op l r .sub) => do
      match ← normalQuadratic₀ l, ← normalQuadratic₀ r with
      -- `some (.inl e₁), some (.inl e₂)`
      | some (.inl e₁), some (.inl e₂) => pure (some (.inl (←(e₁ - e₂))))
      -- `some (.inl e), some (.inr ⟨A, B, C⟩)`
      | some (.inl e'), some (.inr ⟨A, B, C⟩) =>
        -- e - (A * B - C) = (- A) * B - (- (C + e))
        -- TODO(a change from the original code, I am not crazy, am I?)
        let c₀ ← mkConstant (0 : ZMod p)
        pure (some (.inr ⟨(←(c₀ - A)), B, (←(c₀ - (←(C + e'))))⟩))
      -- `some (.inr ⟨A, B, C⟩), some (.inl e₁)`
      | some (.inr ⟨A, B, C⟩), some (.inl e₁) =>
        -- (A * B - C) - e₁ -> A * B - (C + e₁)
        pure (some (.inr ⟨A, B, (←(C + e₁))⟩))
      -- `_, _`
      | _, _ => pure none
    -- `.mul l r`
    | some (.binary_op l r .mul) => do
      match ← normalQuadratic₀ l, ← normalQuadratic₀ r with
      | some (.inl e₁), some (.inl e₂) =>
        let σ' ← getThe (HashConsSt p)
        match σ'[e₁]?, σ'[e₂]? with
        -- `some (.inl e₁@(.c _)), some (.inl e₂@(.v _))`
        | some (.c _), some (.v _)
        -- `some (.inl e₁@(.v _)), some (.inl e₂@(.c _))`
        | some (.v _), some (.c _) => pure (some (.inl (←(e₁ * e₂))))
        -- `some (.inl e₁), some (.inl e₂)`
        | _, _ => pure (some (.inr ⟨e₁, e₂, (←mkConstant (0 : ZMod p))⟩))
      -- `_, _`
      | _, _ => pure none
  modify (·.insert e res)
  return res
termination_by e
decreasing_by
  all_goals
    have h_lt : e < σ.exprs.size := by
      by_contra h_ge
      simp_all
    have := σ.wellFormed e h_lt
    simp_all [CacheExpr.wellFormed]

/--
Linearity of an expression as defined at
https://docs.circom.io/circom-language/constraint-generation/

"Linear expression: an expression where only addition is used. It can also be
written using multiplication of variables by constants. For instance, the
expression `2*x + 3*y + 2` is allowed, as it is equivalent to
`x + x + y + y + y + 2`."
-/
def isLinear (e : BoundRef p) : MemoM p Bool Bool := do
  if let some res := (← get)[e]? then return res
  let σ ← getThe (HashConsSt p)
  let res ←
    match _ : σ[e]? with
    | none => pure false
    -- `.v _` and `.c _`
    | some (.v _)
    | some (.c _) => pure true
    -- `.add e₁ e₂ | .sub e₁ e₂`
    | some (.binary_op l r .add)
    | some (.binary_op l r .sub) => do
      -- Short-circuit `&&`
      if ← isLinear l then isLinear r else pure false
    | some (.binary_op l r .mul) =>
      match σ[l]?, σ[r]? with
      -- `.mul (.c _) (.v _)`
      | some (.c _), some (.v _)
      -- `.mul (.v _) (.c _)`
      | some (.v _), some (.c _) => pure true
      -- `.mul _ _`
      | _, _ => pure false
  modify (·.insert e res)
  return res
termination_by e
decreasing_by
  all_goals
    have h_lt : e < σ.exprs.size := by
      by_contra h_ge
      simp_all
    have := σ.wellFormed e h_lt
    simp_all [CacheExpr.wellFormed]

section Test

section Wheels

private inductive ValExpr
  | v (_ : ℕ)
  | c (_ : ZMod 7)
  | add (_ _ : ValExpr)
  | sub (_ _ : ValExpr)
  | mul (_ _ : ValExpr)

private def ValExpr.build : ValExpr → HashConsM 7 (BoundRef 7)
  | .v i => mkVar i
  | .c k => mkConstant k
  | .add l r => do (← l.build) + (← r.build)
  | .sub l r => do (← l.build) - (← r.build)
  | .mul l r => do (← l.build) * (← r.build)

private def checkScalarArithmetic₀ (input : ValExpr) (expected : ValExpr ⊕ ZMod 7) : Bool :=
  HashConsM.getResult (σ := HashConsSt.empty 7) do
    let res ← (scalarArithmetic₀ (← input.build)).run' {}
    let expected ← expected.elim (.inl <$> ·.build) (pure ∘ .inr)
    return res == expected

private def checkScalarArithmetic (input expected : ValExpr) : Bool :=
  HashConsM.getResult (σ := HashConsSt.empty 7) do
    let res ← (scalarArithmetic (← input.build)).run' {}
    return res == (← expected.build)

private def checkMulByConstants (input expected : ValExpr) : Bool :=
  HashConsM.getResult (σ := HashConsSt.empty 7) do
    let res ← (mulByConstants (← input.build)).run' {}
    return res == (← expected.build)

private def checkNormalQuadratic₀
  (input : ValExpr) (expected : Option (ValExpr ⊕ ValExpr × ValExpr × ValExpr)) : Bool :=
  HashConsM.getResult (σ := HashConsSt.empty 7) do
    let res ← (normalQuadratic₀ (← input.build)).run' {}
    let expected : Option (BoundRef 7 ⊕ NormalQuadratic 7) ←
      match expected with
      | none => pure none
      | some (.inl t) => pure (some (.inl (← t.build)))
      | some (.inr (A, B, C)) => pure (some (.inr ⟨←A.build, ←B.build, ←C.build⟩))
    return res == expected

private def checkIsLinear (input : ValExpr) : Bool :=
  HashConsM.getResult (σ := HashConsSt.empty 7) do
    (isLinear (← input.build)).run' {}

end Wheels

open ValExpr

private instance : Add ValExpr := ⟨.add⟩
private instance : Sub ValExpr := ⟨.sub⟩
private instance : Mul ValExpr := ⟨.mul⟩
private instance {n : ℕ} : OfNat ValExpr n := ⟨.c n⟩

section

example :
  checkScalarArithmetic₀
    ((4 * 3 - 5 * 2) * v 1 + (1 - (1 + 1)) * v 2)
    (.inl (2 * v 1 + 6 * v 2))
:= by
  native_decide

example :
  checkScalarArithmetic₀
    ((5 * v 1 + (3 + 2) * v 2) * ((1 + 1) * v 1))
    (.inl ((5 * v 1 + 5 * v 2) * (2 * v 1)))
:= by
  native_decide

example :
  checkScalarArithmetic₀
    (2 * (1 + ((2 * 1 + 1 * 2) * 2) + 1) * v 1)
    (.inl (20 * v 1))
:= by
  native_decide

example : checkScalarArithmetic₀ ((1 + 2) * (3 - 1)) (.inr 6) := by native_decide

example :
  checkScalarArithmetic₀
    (let x₁ := v 0 + v 0; let x₂ := x₁ + x₁; x₂ + x₂)
    (.inl (let x₁ := v 0 + v 0; let x₂ := x₁ + x₁; x₂ + x₂))
:= by
  native_decide

end

section

example :
  checkScalarArithmetic ((4 * 3 - 5 * 2) * v 1 + (1 - (1 + 1)) * v 2) (2 * v 1 + 6 * v 2)
:= by
  native_decide

example : checkScalarArithmetic ((1 + 2) * (3 - 1)) 6 := by native_decide

example : checkScalarArithmetic (v 1) (v 1) := by native_decide

end

section

example : checkMulByConstants (3 * (v 1 * 2)) (6 * v 1) := by native_decide

example : checkMulByConstants (2 * (3 * v 1)) (6 * v 1) := by native_decide

example : checkMulByConstants (4 * v 1 * 2 + 2 * v 2 * 4) (8 * v 1 + 8 * v 2) := by native_decide

example :
  checkMulByConstants (2 * (v 1 * 5) + 5 * (v 2 * 2)) (10 * v 1 + 10 * v 2)
:= by
  native_decide

example :
  checkMulByConstants (2 * (3 * v 1 + 1 * v 2) * 2) (12 * v 1 + 4 * v 2)
:= by
  native_decide

example :
  checkMulByConstants (2 * (3 * v 1 * (v 2 * 4))) ((6 * v 1) * (v 2 * 4))
:= by
  native_decide

example : checkMulByConstants (v 1 * 3) (v 1 * 3) := by native_decide

example : checkMulByConstants (2 * 3) 6 := by native_decide

example :
  checkMulByConstants
    (let x₁ := 2 * (v 0 + v 1); let x₂ := x₁ + x₁; x₂ * x₂)
    (let x₁ := 2 * v 0 + 2 * v 1; let x₂ := x₁ + x₁; x₂ * x₂)
:= by
  native_decide

end

section

example : checkNormalQuadratic₀ (v 1) (some (.inl (v 1))) := by native_decide

example : checkNormalQuadratic₀ (2 * v 1 + 3) (some (.inl (2 * v 1 + 3))) := by native_decide

example : checkNormalQuadratic₀ (v 1 * 2) (some (.inl (v 1 * 2))) := by native_decide

example : checkNormalQuadratic₀ (v 1 * v 2) (some (.inr (v 1, v 2, 0))) := by native_decide

example :
  checkNormalQuadratic₀ ((v 1 + 1) * v 2) (some (.inr (v 1 + 1, v 2, 0)))
:= by
  native_decide

example :
  checkNormalQuadratic₀ (v 1 * v 2 - v 3) (some (.inr (v 1, v 2, 0 + v 3)))
:= by
  native_decide

example :
  checkNormalQuadratic₀ (v 3 + v 1 * v 2) (some (.inr (v 1, v 2, 0 - v 3)))
:= by
  native_decide

example :
  checkNormalQuadratic₀ (v 1 * v 2 + v 3) (some (.inr (v 1, v 2, 0 - v 3)))
:= by
  native_decide

example :
  checkNormalQuadratic₀ (v 3 - v 1 * v 2) (some (.inr (0 - v 1, v 2, 0 - (0 + v 3))))
:= by
  native_decide

example : checkNormalQuadratic₀ (v 1 * v 2 * v 3) none := by native_decide

example : checkNormalQuadratic₀ (v 1 * v 2 + v 3 * v 4) none := by native_decide

end

section

example : checkIsLinear (1 + v 1 + 5 * v 3 + v 2 * 2 + 3) = true := by native_decide

example : checkIsLinear (v 5 * v 3) = false := by native_decide

example : checkIsLinear (v 1 * (1 + 1)) = false := by native_decide

example : checkIsLinear (v 1 - 2 * v 2) = true := by native_decide

/--
Following the old design, we expect all constants to be folded a-priori.
-/
example : checkIsLinear (2 * 3) = false := by native_decide

example : checkIsLinear (v 1 + v 1 * v 2 + v 1 * v 2) = false := by native_decide

end

end Test

/--
Turns expressions into `A * B - C` format that R1CS expects.
Here `A, B, C` are all first order.

TODO(note): `numInputs` might not be needed, but we do make a distinction
between public and private inputs

def Cs.toR1CS (cs : Cs' p) : R1CSv1 :=
  quadraticToR1CS (Clap.toLevels cs)

In `old/.../Quadratic.lean`.

We need:
Expression transformations:
- Exp.nVars₀
- Exp.nVars 
- Exp.toCoeff₀ 
- Exp.toCoeff
- Exp.normalQuadratic
Top level guys:
- quadraticToConstraints
- r1csNormalizeGetNVars
- quadraticToR1CS

Optimisations:
- `old/Clap/Cfold.lean`
- `old/Clap/Dedup.lean`
- `old/Clap/Unshare.lean`
-/
def toR1CS (cs : ConstraintSystem p) (numInputs : ℕ) : Option R1CSv1 :=
  sorry

end ConstraintSystem

end Clap
