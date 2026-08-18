import Clap.BitVec

import Clap.eDSLState.Varstore

import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.HashCons.HashConsSt

import Clap.eDSLState.Gate
import Clap.eDSLState.Wheels

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
lemma stupidext {p : ℕ} (st : EvalSt p) :
  st = ⟨st.numAlloc, st.varStore, st.constraints⟩ := rfl

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
  evalM st.varStore e

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

@[grind =]
lemma getElem?_eq_get? : st[e]? = st.get? e := rfl

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

@[grind _=_]
lemma getElem?_eq_evalRec_of_wellFormed (h : e.wellFormed) : st[e]? = e.evalRec st.varStore := by
  grind

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
    (Γ.insertMany ((Vector.range k).map (·+numAlloc) |>.zip vals))
    constraints
:= rfl

variable {k : ℕ} {vars : Vector (ZMod p) k}

@[simp, grind =]
lemma numAlloc_alloc :
  (st.alloc vars).numAlloc = st.numAlloc + k := rfl

@[simp, grind =]
lemma varStore_alloc :
  (st.alloc vars).varStore =
  st.varStore.insertMany ((Vector.range k).map (·+st.numAlloc) |>.zip vars) := rfl

@[simp, grind =]
lemma constraints_alloc :
  (st.alloc vars).constraints = st.constraints := rfl

def step (result : EvalSt p) (next : Gate) (σ : HashConsSt p) : EvalSt p :=
  match next with
  | .eq0 e => result.addConstraint (result[Expr.mk e σ]? = .some 0)
  | .share e => (result.assertAllocated ⟨e, σ⟩).alloc #v[result[Expr.mk e σ]!]
  | .isZero e => (result.assertAllocated ⟨e, σ⟩).alloc #v[if result[Expr.mk e σ]? = Option.some 0 then 1 else 0]
  | .num2bits width e => (result.assertAllocated ⟨e, σ⟩).alloc (num2bitsLsbPureV width (result[Expr.mk e σ]!))

notation "[" res ", " σ "|" cmd "]ₛ" => step res cmd σ

-- TODO do we want to make individual functions for these parts and prove properties about them
@[simp, grind =]
lemma step_mk
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (constraints : Prop)
  (next : Gate)
  (σ : HashConsSt p)
: (EvalSt.mk numAlloc varStore constraints).step next σ =
  match next with
  | Gate.eq0 e => { numAlloc := numAlloc, varStore := varStore, constraints := constraints ∧ [varStore,σ|e] = some 0 }
  | Gate.share e =>
    { numAlloc := numAlloc + 1,
      varStore := varStore.insertMany #v[(numAlloc, [varStore,σ|e].getD 0)],
      constraints := constraints ∧ [varStore,σ|e].isSome = true }
  | Gate.isZero e =>
    { numAlloc := numAlloc + 1,
      varStore := varStore.insertMany #v[(numAlloc, if [varStore,σ|e] = some 0 then 1 else 0)],
      constraints := constraints ∧ [varStore,σ|e].isSome = true }
  | Gate.num2bits width e =>
    { numAlloc := numAlloc + width,
      varStore := varStore.insertMany
          ((Vector.map (fun x => x + numAlloc) (Vector.range width)).zip
            (num2bitsLsbPureV width ([varStore,σ|e].getD 0))),
      constraints := constraints ∧ [varStore,σ|e].isSome = true
    }
:= by
  unfold step
  cases next <;> simp
  rfl

@[simp, grind =]
lemma step_numAlloc
  (next : Gate)
:
  (st.step next σ).numAlloc =
  st.numAlloc + next.numAllocStep
:= by
  grind [=step]

@[simp, grind =]
lemma step_varStore_keys
  (next : Gate)
:
  (st.step next σ).varStore.keys.toFinset =
  st.varStore.keys.toFinset ∪ (List.range' st.numAlloc next.numAllocStep).toFinset
:= by
  cases next <;> simp [step]
  . ext
    simp
    expose_names
    grind
  . ext
    simp
    grind
  . ext
    expose_names
    simp [-Std.ExtTreeMap.mem_insertMany_vector, Vector.range]
    have (k: ℕ) : Array.range k = ⟨List.range k⟩ := by grind
    simp_rw [this]
    simp [-List.toArray_range, Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany]
    rewrite [Vector.foldl_mk]
    unfold Membership.mem Std.ExtTreeMap.instMembershipOfTransCmp Std.ExtTreeMap.contains
    simp
    generalize num2bitsLsbPureV _ _ = data
    induction' w with w h_w
    . simp [Vector.zip, Array.zip_eq_empty_iff.mpr]
    . simp [Vector.zip]
      have : data.toArray = (data.toArray.take w) ++ #[data.toArray.back] := by grind
      rewrite [this]
      have : List.range (w + 1) = List.range w ++ [w] := by grind
      rewrite [this]
      simp only [List.map_append, List.map_cons, List.map_nil, ←List.append_toArray]
      rewrite [Array.zip_append (by grind)]
      simp
      specialize h_w data.pop
      simp [Vector.pop] at h_w
      simp [h_w]
      constructor
      . intro h
        obtain h | h := h
        . grind
        . grind
      . grind


variable {σ : HashConsSt p} {gate : Gate}

lemma step_unconstrained :
  [unconstrained[numAlloc][Γ], σ|gate]ₛ =
  [⟨numAlloc, Γ, True⟩, σ|gate]ₛ := rfl

def split (result : EvalSt p) : EvalSt p :=
  {result with constraints := True}

@[simp, grind =]
lemma numAlloc_split : st.split.numAlloc = st.numAlloc := rfl

@[simp, grind =]
lemma varStore_split : st.split.varStore = st.varStore := rfl

@[simp, grind =]
lemma constraints_split : st.split.constraints = True := rfl

@[simp, grind =]
lemma step_eq0 :
  [st,σ|.eq0 e!]ₛ = st.addConstraint (st[Expr.mk e! σ]? = .some 0) := rfl

@[simp, grind =]
lemma step_share :
  [st, σ|.share e!]ₛ =
  (st.assertAllocated ⟨e!, σ⟩ |>.alloc #v[st.getD ⟨e!, σ⟩]) := rfl

@[simp, grind =]
lemma step_isZero :
  [st, σ|.isZero e!]ₛ =
  (st.assertAllocated ⟨e!, σ⟩ |>.alloc #v[if st[(⟨e!, σ⟩ : Expr _)]? = .some 0 then 1 else 0]) := rfl

@[simp, grind =]
lemma step_num2bits {width} :
  [st, σ|.num2bits width e!]ₛ =
  (st.assertAllocated ⟨e!, σ⟩ |>.alloc (num2bitsLsbPureV width st[Expr.mk e! σ]!)) := rfl

@[aesop unsafe, grind =]
lemma addConstraint_eq_mk :
  st.addConstraint constraint =
  ⟨st.numAlloc, st.varStore, st.constraints ∧ constraint⟩ := rfl

@[aesop unsafe, grind =]
lemma allocAnonymous_eq_mk :
  st.allocAnonymous =
  ⟨st.numAlloc + 1, st.varStore, st.constraints⟩ := rfl

lemma alloc_eq_mk {k} {vals : Vector _ k} :
  st.alloc vals =
  ⟨st.numAlloc + k,
   st.varStore.insertMany (((Vector.range k).map (· + st.numAlloc)).zip vals),
   st.constraints⟩ := rfl

lemma assertAllocated_eq_addConstraint :
  st.assertAllocated e = st.addConstraint (e ∈ st) := rfl

end EvalSt

end EvalSt

end Clap
