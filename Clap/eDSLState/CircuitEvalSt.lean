import Clap.eDSLState.Varstore

import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.HashCons.HashConsSt

namespace Clap

open HashConsM

structure EvalSt (p : ℕ) where
  numAlloc : ℕ
  varStore : VarStore p
  constraints : Prop
  deriving Inhabited

namespace EvalSt

/--
Hic sunt dracones.

TODO: Nuke this
-/
lemma stupidext {p : ℕ} (result : EvalSt p) :
  result = ⟨result.numAlloc, result.varStore, result.constraints⟩ := rfl

section EvalSt

variable {p numAlloc : ℕ} {Γ : VarStore p} {st : EvalSt p} {constraints constraint : Prop}

def empty (p : ℕ) : EvalSt p := ⟨0, ∅, True⟩

def unconstrained (numAlloc : ℕ) (Γ : VarStore p) : EvalSt p :=
  ⟨numAlloc, Γ, True⟩

notation
  "unconstrained[" numAlloc:arg "]" "[" varStore:arg "]" => unconstrained numAlloc varStore

@[simp, grind =]
lemma numAlloc_unconstrained : unconstrained[numAlloc][Γ].numAlloc = numAlloc := rfl

@[simp, grind =]
lemma varStore_unconstrained : unconstrained[numAlloc][Γ].varStore = Γ := rfl

@[simp, grind =]
lemma constraints_unconstrained : unconstrained[numAlloc][Γ].constraints = True := rfl

def addConstraint (st : EvalSt p) (constraint : Prop) : EvalSt p :=
  {st with constraints := st.constraints ∧ constraint}

@[simp, grind =]
lemma addConstraint_mk
:
  (EvalSt.mk numAlloc Γ constraints).addConstraint constraint =
  EvalSt.mk numAlloc Γ (constraints ∧ constraint)
:= rfl

@[simp, grind =]
lemma addConstraint_unconstrained :
  unconstrained[numAlloc][Γ].addConstraint constraint =
  ⟨numAlloc, Γ, constraint⟩ := by simp [unconstrained]

@[simp, grind =]
lemma numAlloc_addConstraint : (st.addConstraint constraint).numAlloc = st.numAlloc := rfl

@[simp, grind =]
lemma varStore_addConstraint : (st.addConstraint constraint).varStore = st.varStore := rfl

@[simp, grind =]
lemma constraints_addConstraint : (st.addConstraint constraint).constraints =
                                  (st.constraints ∧ constraint) := rfl

def allocAnonymous (st : EvalSt p) : EvalSt p :=
  {st with numAlloc := st.numAlloc + 1}

@[simp, grind =]
lemma allocAnonymous_mk
:
  (EvalSt.mk numAlloc Γ constraints).allocAnonymous =
  EvalSt.mk (numAlloc + 1) Γ constraints
:= rfl

@[simp, grind =]
lemma allocAnonymous_unconstrained :
  unconstrained[numAlloc][Γ].allocAnonymous =
  ⟨numAlloc + 1, Γ, True⟩ := rfl

@[simp, grind =]
lemma numAlloc_allocAnonymous : st.allocAnonymous.numAlloc = st.numAlloc + 1 := rfl

@[simp, grind =]
lemma varStore_allocAnonymous : st.allocAnonymous.varStore = st.varStore := rfl

@[simp, grind =]
lemma constraints_allocAnonymous : st.allocAnonymous.constraints = st.constraints := rfl

@[grind =]
def get? (st : EvalSt p) (e : Expr p) : Option (ZMod p) := do
  [st.varStore|e]

@[grind =]
def getM? (st : EvalSt p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  HashConsM.evalM st.varStore e

instance : Membership (Expr p) (EvalSt p) :=
  ⟨fun Γ e ↦ (get? Γ e).isSome⟩

instance : GetElem (EvalSt p) (Expr p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
  ⟨fun circuitResult e h ↦ circuitResult.get? e |>.get h⟩

def getD (result : EvalSt p) (e : Expr p) : ZMod p :=
  (result.get? e).getD 0

instance : GetElem? (EvalSt p) (Expr p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
  ⟨get?, getD⟩

def getDM (result : EvalSt p) (e : HashConsM p ExprRef) : HashConsM p (ZMod p) := do
  result.getM? e <&> Option.getD (dflt := 0)

variable {e! : ExprRef} {σ : HashConsSt p} {eM : HashConsM p ExprRef} {e : Expr p}

@[simp, grind =]
lemma getD_eq_getM?_getD : st.getD e = (st[e]?).getD 0 := rfl

@[simp, grind =]
lemma getElem!_eq_getElem?_getD : st[e]! = (st[e]?).getD 0 := rfl

@[simp, grind =]
lemma getDM_eq_getM?_getD : st.getDM eM = st.getM? eM <&> Option.getD (dflt := 0) := rfl

@[simp, grind =]
lemma get?_mk
:
  (EvalSt.mk numAlloc Γ constraints).get? e = [Γ|e]
:= rfl

@[simp, grind =]
lemma getM?_mk
:
  ((EvalSt.mk numAlloc Γ constraints).getM? eM).run σ = [Γ,σ|←eM]
:= rfl

@[simp, grind =]
lemma getElem?_mk
:
  (EvalSt.mk numAlloc Γ constraints)[e]? = [Γ|e]
:= rfl

@[simp, grind =]
lemma membership_unconstrained
:
  (e ∈ unconstrained[numAlloc][Γ]) = [Γ|e].isSome
:= rfl

@[simp, grind =]
lemma getElem?_unconstrained
:
  unconstrained[numAlloc][Γ][e]? = [Γ|e]
:= rfl

@[simp, grind =]
lemma getM?_unconstrained:
  (unconstrained[numAlloc][Γ].getM? eM).run σ = [Γ,σ|←eM] := by
  simp [unconstrained]

@[grind =_]
lemma getM?_unconstrained_eq_getM?_mk :
  (unconstrained[numAlloc][Γ].getM? eM).run σ =
  ((EvalSt.mk numAlloc Γ constraints).getM? eM).run σ := by grind

variable {st' : EvalSt p}

@[grind =>]
lemma get?_of_varStore_eq_varStore (h : st.varStore = st'.varStore)
:
  st.get? e = st'.get? e
:= by grind

@[grind =>]
lemma getElem?_of_varStore_eq_varStore (h : st.varStore = st'.varStore)
:
  st[e]? = st'[e]?
:= get?_of_varStore_eq_varStore h

@[grind =>]
lemma getM?_of_varStore_eq_varStore (h : st.varStore = st'.varStore) :
  st.getM? eM = st'.getM? eM := by
  simp_all [EvalSt.getM?]

/--
Asserts that the expression that e points to does not use any variables that aren't in the varStore
Panics if e is outside of σ
-/
def assertAllocated (st : EvalSt p) (e : Expr p) : EvalSt p :=
  st.addConstraint st[e]?.isSome

def assertAllocatedM (st : EvalSt p) (e : HashConsM p ExprRef) : HashConsM p (EvalSt p) := do
  let val ← st.getM? e
  return st.addConstraint val.isSome

@[simp, grind =]
lemma assertAllocated_mk
:
  (EvalSt.mk numAlloc Γ constraints).assertAllocated e =
  EvalSt.mk numAlloc Γ (constraints ∧ [Γ|e].isSome)
:= rfl

@[simp, grind =]
lemma assertAllocatedM_mk
:
  ((EvalSt.mk numAlloc Γ constraints).assertAllocatedM eM).run σ =
  (
    EvalSt.mk
      numAlloc
      Γ
      (constraints ∧ [Γ,σ|←eM].1.isSome)
    ,
    [Γ,σ|←eM].2
  )
:= rfl

@[simp, grind =]
lemma numAlloc_assertAllocated :
  (st.assertAllocated e).numAlloc = st.numAlloc := rfl

@[simp, grind =]
lemma varStore_assertAllocated :
  (st.assertAllocated e).varStore = st.varStore := rfl

@[simp, grind =]
lemma constraints_assertAllocated :
  (st.assertAllocated e).constraints = (st.constraints ∧ st[e]?.isSome) := rfl

@[simp, grind =]
lemma assertAllocated_unconstrained :
  unconstrained[numAlloc][Γ].assertAllocated e =
  letI α := unconstrained[numAlloc][Γ]
  α.addConstraint (e ∈ α) := rfl

def alloc {k p : ℕ} (result : EvalSt p) (vals : Vector (ZMod p) k) : EvalSt p :=
  let indexed := (Vector.range k).map (·+result.numAlloc) |>.zip vals
  let varStore := result.varStore.insertMany indexed
  {result with varStore := varStore, numAlloc := result.numAlloc + k}

@[simp, grind =]
lemma alloc_mk
  {k : ℕ}
  {vals : Vector (ZMod p) k}
:
  (EvalSt.mk numAlloc Γ constraints).alloc vals =
  EvalSt.mk
    (numAlloc + k)
    (varStore.insertMany ((Vector.range k).map (·+numAlloc) |>.zip vals))
    constraints
:= rfl

@[simp, grind =]
lemma numAlloc_alloc :
  (result.alloc vars).numAlloc = result.numAlloc + k := rfl

@[simp, grind =]
lemma varStore_alloc :
  (result.alloc vars).varStore =
  result.varStore.insertMany ((Vector.range k).map (·+result.numAlloc) |>.zip vars) := rfl

@[simp, grind =]
lemma constraints_alloc {vars : Vector (ZMod p) k} :
  (result.alloc vars).constraints = result.constraints := rfl

def step (result : CircuitResult p) (next : Gate p) (σ : HashConsSt p) : CircuitResult p :=
  match next with
  | .eq0 e => result.addConstraint (result[(e, σ)]? = Option.some 0)
  | .share e => (result.assertAllocated e σ).alloc #v[result[(e, σ)]!]
  | .isZero e => (result.assertAllocated e σ).alloc #v[if result[(e, σ)]? = Option.some 0 then 1 else 0]
  | .num2bits width e => (result.assertAllocated e σ).alloc (num2bitsLsbPureV width (result[(e, σ)]!))

notation "[" res ", " σ "|" cmd "]ₛ" => step res cmd σ

end EvalSt

end EvalSt

end Clap
