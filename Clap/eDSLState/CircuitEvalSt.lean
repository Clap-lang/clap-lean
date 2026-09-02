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

@[grind _=_]
lemma mem_def {e : Expr p} : e ∈ st ↔ (st[e]?.isSome = true) := by rfl

@[grind .]
lemma getElem?_eq_of_varStore_eq
  {st1 st2 : EvalSt p}
  {e : Expr p}
  (h_eq : st1.varStore = st2.varStore)
:
  st1[e]? = st2[e]?
:= by
  unfold_projs
  unfold get?
  grind

@[grind .]
lemma mem_eq_of_varStore_eq
  {st1 st2 : EvalSt p}
  {e : Expr p}
  (h_eq : st1.varStore = st2.varStore)
:
  e ∈ st1 ↔ e ∈ st2
:= by
  rewrite [mem_def, mem_def]
  grind

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

lemma getElem?_eq_evalRec_of_wellFormed (h : e.wellFormed) : st[e]? = e.evalRec st.varStore := by
  grind [eval_eq_evalRec]

@[grind =>]
lemma getM?_of_varStore_eq_varStore (h : st.varStore = st'.varStore) :
  st.getM? eM = st'.getM? eM := by
  simp_all [EvalSt.getM?]

/--
Asserts that the expression that e points to does not use any variables that aren't in the varStore
Panics if e is outside of σ
-/
def assertAllocated {k} (st : EvalSt p) (es : Vector (Expr p) k) : EvalSt p :=
  st.addConstraint (∀ e ∈ es, e ∈ st)

section AssertAllocated

variable {k : ℕ} {es : Vector (Expr p) k}

@[simp, grind =]
lemma assertAllocated_mk :
  (EvalSt.mk numAlloc Γ constraints).assertAllocated es =
  EvalSt.mk numAlloc Γ (constraints ∧ ∀ e ∈ es, [Γ|e].isSome) := rfl

@[simp, grind =]
lemma numAlloc_assertAllocated {k} {es : Vector (Expr p) k} :
  (st.assertAllocated es).numAlloc = st.numAlloc := rfl

@[simp, grind =]
lemma varStore_assertAllocated :
  (st.assertAllocated es).varStore = st.varStore := rfl

@[simp, grind =]
lemma constraints_assertAllocated :
  (st.assertAllocated es).constraints = (st.constraints ∧ ∀ e ∈ es, e ∈ st) := rfl

@[simp, grind =]
lemma assertAllocated_unconstrained :
  unconstrained[numAlloc][Γ].assertAllocated es =
  letI α := unconstrained[numAlloc][Γ]
  α.addConstraint (∀ e ∈ es, e ∈ α) := rfl

end AssertAllocated

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

def fpMulPureV (w k : ℕ) (a b p' : Vector (ZMod p) k) : Vector (ZMod p) k :=
  let a_val : ℕ := ∑ i : Fin k, a[i].val * (2^w)^i.val
  let b_val : ℕ := ∑ i : Fin k, b[i].val * (2^w)^i.val
  let p'_val : ℕ := ∑ i : Fin k, p'[i].val * (2^w)^i.val
  let res_val : ℕ := (a_val * b_val) % p'_val
  natToLimbsV p w k res_val

-- def eval : Circuitₑ p → denotation (ZMod p)
--   | .nil =>
--       .u
--   | .lam k =>
--       .l fun x => eval (k x)
--   | .eq0 e c =>
--       if e.eval = 0 then eval c else .n
--   | .share e k =>
--       (k e.eval).eval
--   | .isZero e k =>
--       if e.eval = 0 then (k 1).eval else (k 0).eval
--   | .num2bits w e k =>
--       if e.eval.val < 2^w then (k (num2bitsLsbPure w e.eval)).eval else .n
--   | .fpmul w k a b p' cont =>
--     if
--       (∀ i : Fin k, a[i].eval.val < 2 ^ w) ∧
--       (∀ i : Fin k, b[i].eval.val < 2 ^ w) ∧
--       (∀ i : Fin k, p'[i].eval.val < 2 ^ w)
--     then
--       let a_val : ℕ := ∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1
--       let b_val : ℕ := ∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1
--       let p_val : ℕ := ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1
--       let res_val : ℕ := (a_val * b_val) % p_val
--       (cont (nat2words p w k res_val)).eval
--     else .n

section step

variable {numAlloc w : ℕ}
         {varStore : VarStore p}
         {constraints : Prop}
         {next : Gate}
         {σ : HashConsSt p}
         {e! : ExprRef}
         {st : EvalSt p}

def stepEq0 (st : EvalSt p) (σ : HashConsSt p) (e : ExprRef) :=
  st.addConstraint (st[Expr.mk e σ]? = .some 0)

@[simp, grind =]
lemma stepEq0_mk :
  (EvalSt.mk numAlloc varStore constraints).stepEq0 σ e! =
  {
    numAlloc := numAlloc,
    varStore := varStore,
    constraints := constraints ∧ [varStore,σ|e!] = some 0
  } := rfl

@[simp, grind =]
lemma numAlloc_stepEq0 : (st.stepEq0 σ e!).numAlloc = st.numAlloc := rfl

@[simp, grind =]
lemma varStore_stepEq0 : (st.stepEq0 σ e!).varStore = st.varStore := rfl

@[simp, grind =]
lemma constraints_stepEq0 : (st.stepEq0 σ e!).constraints =
                            (st.constraints ∧ st[Expr.mk e! σ]? = some 0) := by
  simp [stepEq0]

def stepShare (st : EvalSt p) (σ : HashConsSt p) (e : ExprRef) :=
  (st.assertAllocated #v[⟨e, σ⟩]).alloc #v[st[Expr.mk e σ]!]

@[simp, grind =]
lemma stepShare_mk :
  (EvalSt.mk numAlloc varStore constraints).stepShare σ e! =
  {
    numAlloc := numAlloc + 1,
    varStore := varStore.insertMany #v[(numAlloc, [varStore,σ|e!].getD 0)],
    constraints := constraints ∧ [varStore,σ|e!].isSome
  } := by simp [stepShare]

@[simp, grind =]
lemma numAlloc_stepShare : (st.stepShare σ e!).numAlloc = st.numAlloc + 1 := rfl

@[simp, grind =]
lemma varStore_stepShare :
  (st.stepShare σ e!).varStore =
  st.varStore.insertMany #v[(st.numAlloc, st[Expr.mk e! σ]?.getD 0)] := by
  simp [stepShare]

@[simp, grind =]
lemma constraints_stepShare : (st.stepShare σ e!).constraints =
                              (st.constraints ∧ ⟨e!, σ⟩ ∈ st) := by
  simp [stepShare]

def stepIsZero (st : EvalSt p) (σ : HashConsSt p) (e : ExprRef) :=
  (st.assertAllocated #v[⟨e, σ⟩]).alloc #v[if st[Expr.mk e σ]? = .some 0 then 1 else 0]

@[simp, grind =]
lemma stepIsZero_mk :
  (EvalSt.mk numAlloc varStore constraints).stepIsZero σ e! =
  {
    numAlloc := numAlloc + 1,
    varStore := varStore.insertMany #v[(numAlloc, if [varStore,σ|e!] = some 0 then 1 else 0)],
    constraints := constraints ∧ [varStore,σ|e!].isSome
  } := by simp [stepIsZero]; rfl

@[simp, grind =]
lemma numAlloc_stepIsZero : (st.stepIsZero σ e!).numAlloc = st.numAlloc + 1 := rfl

@[simp, grind =]
lemma varStore_stepIsZero :
  (st.stepIsZero σ e!).varStore =
  st.varStore.insertMany #v[(st.numAlloc, if st[Expr.mk e! σ]? = some 0 then 1 else 0)] := by
  simp [stepIsZero]

@[simp, grind =]
lemma constraints_stepIsZero : (st.stepIsZero σ e!).constraints =
                               (st.constraints ∧ ⟨e!, σ⟩ ∈ st) := by
  simp [stepIsZero]

def stepNum2bits (st : EvalSt p) (σ : HashConsSt p) (w : ℕ) (e : ExprRef) :=
  (st.assertAllocated #v[⟨e, σ⟩]).alloc (num2bitsLsbPureV w (st[Expr.mk e σ]!))

@[simp, grind =]
lemma stepNum2bits_mk :
  (EvalSt.mk numAlloc varStore constraints).stepNum2bits σ w e! =
  {
    numAlloc := numAlloc + w,
    varStore := varStore.insertMany
      ((Vector.map (fun x => x + numAlloc) (Vector.range w)).zip
        (num2bitsLsbPureV w ([varStore,σ|e!].getD 0))),
    constraints := constraints ∧ [varStore,σ|e!].isSome
  } := by simp [stepNum2bits]

@[simp, grind =]
lemma numAlloc_stepNum2bits : (st.stepNum2bits σ w e!).numAlloc = st.numAlloc + w := rfl

@[simp, grind =]
lemma varStore_stepNum2bits {w} :
  (st.stepNum2bits σ w e!).varStore =
  st.varStore.insertMany
    ((Vector.map (fun x => x + st.numAlloc) (Vector.range w)).zip
      (num2bitsLsbPureV w (st[Expr.mk e! σ]?.getD 0))) := by
  simp [stepNum2bits]

@[simp, grind =]
lemma constraints_stepNum2bits : (st.stepNum2bits σ w e!).constraints =
                                 (st.constraints ∧ ⟨e!, σ⟩ ∈ st) := by
  simp [stepNum2bits]

def stepFpmul (st : EvalSt p) (σ : HashConsSt p) (w k : ℕ) (a b p' : Vector ExprRef k) :=
  let (aexprs, bexprs, p'exprs) := (a.map (Expr.mk · σ), b.map (Expr.mk · σ), p'.map (Expr.mk · σ))
  let (avals, bvals, p'vals) := (aexprs.map (st[·]!), bexprs.map (st[·]!), p'exprs.map (st[·]!))
  (((((st.assertAllocated (aexprs ++ bexprs ++ p'exprs)
  ).addConstraint (∀ a ∈ aexprs, st[a]!.val < 2^w)
  ).addConstraint (∀ b ∈ bexprs, st[b]!.val < 2^w)
  ).addConstraint (∀ p' ∈ p'exprs, st[p']!.val < 2^w)
  ).addConstraint (0 < ∑ i : Fin k, p'vals[i].val * (2^w)^i.val)
  ).alloc (fpMulPureV w k avals bvals p'vals)

@[simp, grind =]
lemma stepFpmul_mk {a b p'} :
  (EvalSt.mk numAlloc varStore constraints).stepFpmul σ w k a b p' =
  letI lookup! := fun e ↦ [varStore,σ|e].getD 0
  let (avalues, bvalues, p'values) := (a.map lookup!, b.map lookup!, p'.map lookup!)
  {
    numAlloc := numAlloc + k,
    varStore :=
      varStore.insertMany
        ((Vector.map (fun x => x + numAlloc) (Vector.range k)).zip
          (fpMulPureV w k avalues bvalues p'values)),
    constraints := constraints ∧ (∀ e ∈ a ++ b ++ p', [varStore|⟨e, σ⟩].isSome = true)
                               ∧ (∀ e ∈ avalues, e.val < 2 ^ w)
                               ∧ (∀ e ∈ bvalues, e.val < 2 ^ w)
                               ∧ (∀ e ∈ p'values, e.val < 2 ^ w)
                               ∧ (0 < ∑ i : Fin k, p'values[i].val * (2 ^ w) ^ i.val)
  } := by
  unfold stepFpmul
  simp
  aesop (add safe (by grind))

@[simp, grind =]
lemma numAlloc_stepFpmul {a b p'} : (st.stepFpmul σ w k a b p').numAlloc = st.numAlloc + k := rfl

@[simp, grind =]
lemma varStore_stepFpmul {w k} {a b p'} :
  (st.stepFpmul σ w k a b p').varStore =
  letI lookup! := fun e ↦ st[Expr.mk e σ]?.getD 0
  let (avalues, bvalues, p'values) := (a.map lookup!, b.map lookup!, p'.map lookup!)
  st.varStore.insertMany
    ((Vector.map (fun x => x + st.numAlloc) (Vector.range k)).zip
      (fpMulPureV w k avalues bvalues p'values)) := by
  unfold stepFpmul
  aesop (add safe (by grind))

@[simp, grind =]
lemma constraints_stepFpmul {w k} {a b p'} :
  (st.stepFpmul σ w k a b p').constraints =
  letI lookup! := fun e ↦ st[Expr.mk e σ]?.getD 0
  st.constraints ∧ (∀ e ∈ a ++ b ++ p', ⟨e, σ⟩ ∈ st)
                 ∧ (∀ e ∈ a, (lookup! e).val < 2 ^ w)
                 ∧ (∀ e ∈ b, (lookup! e).val < 2 ^ w)
                 ∧ (∀ e ∈ p', (lookup! e).val < 2 ^ w)
                 ∧ (0 < ∑ i : Fin k, (lookup! p'[i]).val * (2 ^ w) ^ i.val) := by
  unfold stepFpmul
  aesop (add safe (by grind))

def step (st : EvalSt p) (next : Gate) (σ : HashConsSt p) : EvalSt p :=
  match next with
  | .eq0      e          => stepEq0 st σ e
  | .share    e          => stepShare st σ e
  | .isZero   e          => stepIsZero st σ e
  | .num2bits w e        => stepNum2bits st σ w e
  | .fpmul    w k a b p' => stepFpmul st σ w k a b p'

@[simp, grind =]
lemma step_eq0 : st.step (.eq0 e!) σ = stepEq0 st σ e! := rfl

@[simp, grind =]
lemma step_share : st.step (.share e!) σ = stepShare st σ e! := rfl

@[simp, grind =]
lemma step_isZero : st.step (.isZero e!) σ = stepIsZero st σ e! := rfl

@[simp, grind =]
lemma step_num2bits {w} : st.step (.num2bits w e!) σ = stepNum2bits st σ w e! := rfl

@[simp, grind =]
lemma step_fpmul {w k a b p'} : st.step (.fpmul w k a b p') σ = stepFpmul st σ w k a b p' := rfl

notation "[" res ", " σ "|" cmd "]ₛ" => step res cmd σ


@[simp, grind =]
lemma step_numAlloc
  {next : Gate}
:
  (st.step next σ).numAlloc =
  st.numAlloc + next.numAllocStep
:= by
  grind

@[simp, grind =]
lemma step_varStore_keys
  {next : Gate}
:
  (st.step next σ).varStore.keys.toFinset =
  st.varStore.keys.toFinset ∪ (List.range' st.numAlloc next.numAllocStep).toFinset
:= by
  cases next <;> simp [step]
  . ext
    simp
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
  · ext
    expose_names
    simp [-Std.ExtTreeMap.mem_insertMany_vector, Vector.range]
    have (k: ℕ) : Array.range k = ⟨List.range k⟩ := by grind
    simp_rw [this]
    simp [-List.toArray_range, Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany]
    rewrite [Vector.foldl_mk]
    unfold Membership.mem Std.ExtTreeMap.instMembershipOfTransCmp Std.ExtTreeMap.contains
    simp
    generalize fpMulPureV _ _ _ _ _ = data
    induction' k with k h_k
    . simp [Vector.zip, Array.zip_eq_empty_iff.mpr]
    . simp [Vector.zip]
      have : data.toArray = (data.toArray.take k) ++ #[data.toArray.back] := by grind
      rewrite [this]
      have : List.range (k + 1) = List.range k ++ [k] := by grind
      rewrite [this]
      simp only [List.map_append, List.map_cons, List.map_nil, ←List.append_toArray]
      rewrite [Array.zip_append]
      · simp
        specialize h_k a.pop b.pop p'.pop data.pop
        simp [Vector.pop] at h_k
        simp [h_k]
        constructor
        . intro h
          obtain h | h := h
          . grind
          . grind
        . grind
      · simp

lemma exists_varStore_step_eq_insertMany
  {st : EvalSt p}
  {gate : Gate}
:
  ∃ k, ∃ (vec : Vector (ℕ × (ZMod p)) k),
    [st, σ|gate]ₛ.varStore = st.varStore.insertMany vec ∧
    ∀ key value, ⟨key, value⟩ ∈ vec → key ≥ st.numAlloc
:= by
  cases gate
  . simp
    use 0, #v[]
    grind
  . expose_names
    simp
    use 1, #v[(st.numAlloc, (st[{{e, σ}}]?.getD 0))]
    rewrite [Std.ExtTreeMap.insert_eq_insertMany_singleton_vec]
    aesop
  . expose_names
    simp
    use 1, #v[(st.numAlloc, (if st[{{e, σ}}]? = some 0 then 1 else 0))]
    rewrite [Std.ExtTreeMap.insert_eq_insertMany_singleton_vec]
    aesop
  . expose_names
    simp
    use w, ((Vector.map (fun x => x + st.numAlloc) (Vector.range w)).zip (num2bitsLsbPureV w (st[{{e, σ}}]?.getD 0)))
    aesop (add safe (by grind [=> Vector.of_mem_zip]))
  . expose_names
    simp
    use k, ((Vector.map (fun x => x + st.numAlloc) (Vector.range k)).zip
          (EvalSt.fpMulPureV w k (Vector.map (fun e => st[{{e, σ}}]?.getD 0) a)
            (Vector.map (fun e => st[{{e, σ}}]?.getD 0) b) (Vector.map (fun e => st[{{e, σ}}]?.getD 0) p')))
    aesop (add safe (by grind [=> Vector.of_mem_zip]))

end step

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

lemma assertAllocated_eq_addConstraint {k} {es : Vector (Expr p) k} :
  st.assertAllocated es = st.addConstraint (∀ e ∈ es, e ∈ st) := rfl

end EvalSt

end EvalSt

end Clap
