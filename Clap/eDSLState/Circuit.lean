import Mathlib.Control.Monad.Writer

import Clap.BitVec
import Clap.eDSLState.HashCons.CacheExpr
import Clap.eDSLState.HashCons.EvalButActuallyGood
import Clap.eDSLState.Varstore

namespace Clap

@[grind cases]
inductive Gate (p : ℕ) where
  | eq0 (e : ExprRef)
  | share (e : ExprRef)
  | isZero (e : ExprRef)
  | num2bits (w : ℕ) (e : ExprRef)

@[grind =]
def Gate.refsValid {p : ℕ} (c : Gate p) (bound : ℕ) : Prop := match c with
  | .eq0 e => e < bound
  | .share e => e < bound
  | .isZero e => e < bound
  | .num2bits _w e => e < bound

@[grind =]
def Gate.varsAllocated {p : ℕ} (c : Gate p) (varStore : VarStore p) (σ : HashConsSt p) : Prop := match c with
    | .eq0 e => [varStore, σ|e].isSome
    | .share e => [varStore, σ|e].isSome
    | .isZero e => [varStore, σ|e].isSome
    | .num2bits _w e => [varStore, σ|e].isSome

section Gate.varsAllocated_lemmas

variable {p : ℕ} {gate : Gate p} {Γ : VarStore p} {σ : HashConsSt p} {e! : ExprRef}

namespace Gate

@[simp, grind =]
lemma varsAllocated_eq0 : varsAllocated (.eq0 e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma varsAllocated_share : varsAllocated (.share e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma varsAllocated_isZero : varsAllocated (.isZero e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma varsAllocated_num2bits {w} : varsAllocated (.num2bits w e!) Γ σ = [Γ, σ|e!].isSome := rfl

end Gate

end Gate.varsAllocated_lemmas

instance {p : ℕ} {c : Gate p} {varStore : VarStore p} {σ : HashConsSt p} :
  Decidable (c.varsAllocated varStore σ) := by
  unfold Gate.varsAllocated
  rcases c <;> infer_instance 

instance {p: ℕ} {x : Gate p} {bound : ℕ}: Decidable (x.refsValid bound) := match x with
  | .eq0 e => e.decLt bound
  | .share e => e.decLt bound
  | .isZero e => e.decLt bound
  | .num2bits _w e => e.decLt bound

abbrev Circuit (p : ℕ) := Array (Gate p)

@[grind =]
def Circuit.refsValid {p : ℕ} (c : Circuit p) (bound : ℕ) : Prop :=
  c.all λ x => (decide (x.refsValid bound))

@[grind =]
def Circuit.varsAllocated {p : ℕ} (c : Circuit p) (varStore : VarStore p) (σ : HashConsSt p) (pc : ℕ) : Prop :=
  ∀ i ≤ pc, c[i]?.any fun instr ↦ instr.varsAllocated varStore σ

structure State where
  numAlloc : ℕ
  pc : ℕ
deriving Inhabited

namespace State

def addAlloc (st : State) (k : ℕ) : State :=
  {st with numAlloc := st.numAlloc + k}

def bumpAlloc (st : State) : State :=
  st.addAlloc 1

def addPc (st : State) (k : ℕ) : State :=
  {st with pc := st.pc + k}

def bumpPc (st : State) : State :=
  st.addPc 1

section Lemmas

variable {st : State}

lemma bumpPc_eq : st.bumpPc = {st with pc := st.pc + 1} := rfl

end Lemmas

end State

-- isZero : input → Bool
-- need to allocate the output of this thing
-- the input is index 0, the output is index 1
-- this becomes 2x eq0 (this needs an auxiliary thing, the inverse or some such)
-- thus, wire 0 maps to 0 when you go down to cs
-- 1 maps to 2, and the inverse becomes 1
-- this 'invalidates' the mapping between input | output (careful)
-- this shift is statically known (we know that isZero will need an extra thing -
-- as such, we can already bump by two, if we so desire - thus, we'll keep 1:1 mapping between input|output)

namespace Edsl

structure CircuitResult (p : ℕ) where
  st : State
  varStore : VarStore p
  constraints : Prop
  deriving Inhabited

namespace CircuitResult

section

-- TODO do we need all of these?
variable {p k numAlloc : ℕ} {result result' : CircuitResult p} {st : State}
         {constraint constraints : Prop} {vars : Vector (ZMod p) k} {e : HashConsM p ExprRef} {e! : ExprRef}
         {varStore : VarStore p}
         {σ : HashConsSt p} {vars : Vector (ZMod p) k}

def init (p : ℕ) : CircuitResult p := ⟨⟨0, 0⟩, ∅, True⟩

def unconstrained (st : State) (varStore : VarStore p) : CircuitResult p :=
  ⟨st, varStore, True⟩

@[grind =]
def bumpPc {p : ℕ} (result : CircuitResult p) : CircuitResult p :=
  {result with st := result.st.bumpPc}

variable {result : CircuitResult p}

notation (name := notationα) "unconstrained[" numAlloc:arg "]" "[" varStore:arg "]" => unconstrained numAlloc varStore

recommended_spelling "unconstrained" for "α" in [unconstrained, notationα]

@[simp, grind =]
lemma numAlloc_unconstrained : unconstrained[st][varStore].st = st := rfl

@[simp, grind =]
lemma varStore_unconstrained : unconstrained[st][varStore].varStore = varStore := rfl

@[simp, grind =]
lemma constraints_unconstrained : unconstrained[st][varStore].constraints = True := rfl

def addConstraint (result : CircuitResult p) (constraint : Prop) : CircuitResult p :=
  {result with constraints := result.constraints ∧ constraint}

@[simp, grind =]
lemma addConstraint_mk
  {constraints constraint : Prop}
:
  (Edsl.CircuitResult.mk st varStore constraints).addConstraint constraint =
  Edsl.CircuitResult.mk st varStore (constraints ∧ constraint)
:= rfl

@[simp, grind =]
lemma addConstraint_unconstrained {constraint : Prop} :
  unconstrained[st][varStore].addConstraint constraint =
  ⟨st, varStore, constraint⟩ := by simp [unconstrained]

@[simp, grind =]
lemma numAlloc_addConstraint : (result.addConstraint constraint).st = result.st := rfl

@[simp, grind =]
lemma varStore_addConstraint : (result.addConstraint constraint).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_addConstraint : (result.addConstraint constraint).constraints =
                                  (result.constraints ∧ constraint) := rfl

def allocAnonymous (result : CircuitResult p) : CircuitResult p :=
  {result with st := result.st.bumpAlloc}

@[simp, grind =]
lemma allocAnonymous_mk
:
  (Edsl.CircuitResult.mk st varStore constraints).allocAnonymous =
  Edsl.CircuitResult.mk st.bumpAlloc varStore constraints
:= rfl

@[simp, grind =]
lemma allocAnonymous_unconstrained :
  unconstrained[st][varStore].allocAnonymous =
  ⟨st.bumpAlloc, varStore, True⟩ := rfl

@[simp, grind =]
lemma numAlloc_allocAnonymous : result.allocAnonymous.st = result.st.bumpAlloc := rfl

@[simp, grind =]
lemma varStore_allocAnonymous : result.allocAnonymous.varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_allocAnonymous : result.allocAnonymous.constraints = result.constraints := rfl

@[grind =]
def get? (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : (Option (ZMod p)) := do
  HashConsM.eval result.varStore e σ

@[grind =]
def getM? (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  HashConsM.evalM result.varStore e

instance : Membership (ExprRef × HashConsSt p) (CircuitResult p) :=
  ⟨fun Γ (x, σ) ↦ (get? Γ x σ).isSome⟩

instance : GetElem (CircuitResult p) (ExprRef × HashConsSt p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
  ⟨fun Γ (x, σ) h ↦ Γ.get? x σ |>.get h⟩

def getD (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : ZMod p :=
  (result.get? e σ).getD (dflt := 0)

instance {p} : GetElem? (CircuitResult p) (ExprRef × HashConsSt p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
  ⟨Function.uncurry ∘ get?, Function.uncurry ∘ getD⟩

def getDM (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (ZMod p) := do
  result.getM? e <&> Option.getD (dflt := 0)

@[simp, grind =]
lemma getD_eq_getM?_getD {e : ExprRef} : result.getD e σ = (result[(e, σ )]?).getD (dflt := 0) := rfl

@[simp, grind =]
lemma getElem!_eq_getElem?_getD {e : ExprRef} : result[(e, σ)]! = (result[(e, σ)]?).getD (dflt := 0) := rfl

@[simp, grind =]
lemma getDM_eq_getM?_getD : result.getDM e = result.getM? e <&> Option.getD (dflt := 0) := rfl

@[simp, grind =]
lemma get?_mk
:
  (Edsl.CircuitResult.mk st varStore constraints).get? e! σ =
  [varStore,σ|e!]
:= rfl

@[simp, grind =]
lemma getM?_mk
:
  ((Edsl.CircuitResult.mk st varStore constraints).getM? e).run σ =
  [varStore,σ|←e]
:= rfl

@[simp, grind =]
lemma getElem?_mk
:
  (Edsl.CircuitResult.mk st varStore constraints)[(e!, σ)]? =
  [varStore,σ|e!]
:= rfl

@[simp, grind =]
lemma membership_unconstrained
:
  ((e!, σ) ∈ unconstrained[st][varStore]) = [varStore,σ|e!].isSome
:= rfl

@[simp, grind =]
lemma getElem?_unconstrained
:
  unconstrained[st][varStore][(e!, σ)]? = [varStore,σ|e!]
:= rfl

@[simp, grind =]
lemma getM?_unconstrained:
  (unconstrained[st][varStore].getM? e).run σ =
  [varStore,σ|←e] := by simp [unconstrained]

@[grind =>]
lemma getElem?_of_varStore_eq_varStore {e : ExprRef} (h : result.varStore = result'.varStore)
:
  result[(e, σ)]? = result'[(e, σ)]?
:= by
  simp_all [GetElem?.getElem?, CircuitResult.get?]

@[grind =>]
lemma getM?_of_varStore_eq_varStore (h : result.varStore = result'.varStore) : result.getM? e = result'.getM? e := by
  simp_all [CircuitResult.getM?]

-- Asserts that the expression that e points to does not use any variables that aren't in the varStore
-- Panics if e is outside of σ
def assertAllocated (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : CircuitResult p :=
  let val := result[(e, σ)]?
  result.addConstraint val.isSome

def assertAllocatedM (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (CircuitResult p) := do
  let val ← result.getM? e
  return result.addConstraint val.isSome

@[simp, grind =]
lemma assertAllocated_mk
:
  (Edsl.CircuitResult.mk st varStore constraints).assertAllocated e! σ =
  Edsl.CircuitResult.mk
    st
    varStore
    (constraints ∧ [varStore,σ|e!].isSome)
:= rfl

@[simp, grind =]
lemma assertAllocatedM_mk
:
  ((Edsl.CircuitResult.mk st varStore constraints).assertAllocatedM e).run σ =
  (
    Edsl.CircuitResult.mk
      st
      varStore
      (constraints ∧ [varStore,σ|←e].1.isSome)
    ,
    [varStore,σ|←e].2
  )
:= rfl

@[simp, grind =]
lemma numAlloc_assertAllocated :
  (result.assertAllocated e! σ).st = result.st := rfl

@[simp, grind =]
lemma varStore_assertAllocated :
  (result.assertAllocated e! σ).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_assertAllocated :
  (result.assertAllocated e! σ).constraints = (result.constraints ∧ result[(e!, σ)]?.isSome) := rfl

@[simp, grind =]
lemma assertAllocated_unconstrained :
  unconstrained[st][varStore].assertAllocated e! σ =
  letI α := unconstrained[st][varStore]
  α.addConstraint ((e!, σ) ∈ α) := rfl

def alloc {k p : ℕ} (result : CircuitResult p) (vals : Vector (ZMod p) k) : CircuitResult p :=
  let indexed := (Vector.range k).map (·+result.st.numAlloc) |>.zip vals
  let varStore := result.varStore.insertMany indexed
  {result with varStore := varStore, st := result.st.addAlloc k}

@[simp, grind =]
lemma alloc_mk
  {vals : Vector (ZMod p) k}
:
  (Edsl.CircuitResult.mk st varStore constraints).alloc vals =
  Edsl.CircuitResult.mk
    (st.addAlloc k)
    (varStore.insertMany ((Vector.range k).map (·+st.numAlloc) |>.zip vals))
    constraints
:= rfl

@[simp, grind =]
lemma numAlloc_alloc :
  (result.alloc vars).st = result.st.addAlloc k := rfl

@[simp, grind =]
lemma varStore_alloc :
  (result.alloc vars).varStore =
  result.varStore.insertMany ((Vector.range k).map (·+result.st.numAlloc) |>.zip vars) := rfl

@[simp, grind =]
lemma constraints_alloc {vars : Vector (ZMod p) k} :
  (result.alloc vars).constraints = result.constraints := rfl

def step (result : CircuitResult p) (next : Gate p) (σ : HashConsSt p) : CircuitResult p :=
  let result :=
    match next with
    | .eq0 e => result.addConstraint (result[(e, σ)]? = Option.some 0)
    | .share e => (result.assertAllocated e σ).alloc #v[result[(e, σ)]!]
    | .isZero e => (result.assertAllocated e σ).alloc #v[if result[(e, σ)]? = Option.some 0 then 1 else 0]
    | .num2bits width e => (result.assertAllocated e σ).alloc (num2bitsLsbPureV width (result[(e, σ)]!))
  result.bumpPc



notation "[" res ", " σ "|" cmd "]ₛ" => step res cmd σ

-- -- TODO do we want to make individual functions for these parts and prove properties about them
-- @[simp, grind =]
-- lemma step_mk
--   (numAlloc : ℕ)
--   (varStore : VarStore p)
--   (constraints : Prop)
--   (next : Gate p)
-- : (Edsl.CircuitResult.mk numAlloc varStore constraints).step next =
--   Edsl.CircuitResult.mk
--     (match next with
--       | .eq0 _ => numAlloc
--       | .lam => numAlloc + 1
--       | .share e => numAlloc + 1
--       | .isZero e => numAlloc + 1
--       | .num2bits width _ => numAlloc + width
--     )
--     (match next with
--       | .eq0 _ => varStore
--       | .lam => varStore
--       | .share e => varStore.insert numAlloc ((e.eval varStore).getD 0)
--       | .isZero e => varStore.insert numAlloc (if (e.eval varStore) = .some 0 then 1 else 0)
--       | .num2bits width e => varStore.insertMany
--         ((Vector.map (fun x => x + numAlloc) (Vector.range width)).zip
--           (num2bitsLsbPureV width ((FixedExp.eval varStore e).getD 0)))
--     )
--     (match next with
--       | .eq0 e => constraints ∧ (e.eval varStore) = .some 0
--       | .lam => constraints
--       | .share e => constraints ∧ (e.eval varStore).isSome
--       | .isZero e => constraints ∧ (e.eval varStore).isSome
--       | .num2bits width e => constraints ∧ (e.eval varStore).isSome
--     )
-- := by
--   sorry
--   -- cases next <;> simp [CircuitResult.step, Membership.mem]
--   -- rfl

-- @[simp, grind =]
lemma step_unconstrained {command : Gate p} {σ} :
  [unconstrained[st][varStore], σ|command]ₛ =
  [⟨st, varStore, True⟩, σ|command]ₛ := rfl

def split (result : CircuitResult p) : CircuitResult p :=
  {result with constraints := True}

@[simp, grind =]
lemma numAlloc_split : result.split.st = result.st := rfl

@[simp, grind =]
lemma varStore_split : result.split.varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_split : result.split.constraints = True := rfl

-- section

-- variable {p width : ℕ} {result : CircuitResult p} {e : FixedExp p}

@[simp, grind =]
lemma step_eq0 :
  [result,σ|.eq0 e!]ₛ = (result.addConstraint (result[(e!, σ)]? = .some 0)).bumpPc := rfl

@[simp, grind =]
lemma step_share :
  [result, σ|.share e!]ₛ =
  (result.assertAllocated e! σ |>.alloc #v[result.getD e! σ]).bumpPc := rfl

@[simp, grind =]
lemma step_isZero :
  [result, σ|.isZero e!]ₛ =
  (result.assertAllocated e! σ |>.alloc #v[if result[(e!, σ)]? = .some 0 then 1 else 0]).bumpPc := rfl

@[simp, grind =]
lemma step_num2bits {width} :
  [result, σ|.num2bits width e!]ₛ =
  (result.assertAllocated e! σ |>.alloc (num2bitsLsbPureV width result[(e!, σ)]!)).bumpPc := rfl

@[aesop unsafe, grind =]
lemma addConstraint_eq_mk :
  result.addConstraint constraint =
  ⟨result.st, result.varStore, result.constraints ∧ constraint⟩ := rfl

@[aesop unsafe, grind =]
lemma allocAnonymous_eq_mk :
  result.allocAnonymous =
  ⟨result.st.bumpAlloc, result.varStore, result.constraints⟩ := rfl

lemma alloc_eq_mk {k} {vals : Vector _ k} :
  result.alloc vals =
  ⟨result.st.addAlloc k,
   result.varStore.insertMany (((Vector.range k).map (· + result.st.numAlloc)).zip vals),
   result.constraints⟩ := rfl

lemma assertAllocated_eq_addConstraint :
  result.assertAllocated e! σ = result.addConstraint ((e!, σ) ∈ result) := rfl

end

end CircuitResult

abbrev Circuit.evalInOrder {p : ℕ}
                           (circuit : Circuit p)
                           (σ : HashConsSt p)
                           (result : CircuitResult p) :=
  circuit.foldl (CircuitResult.step (σ := σ)) result (start := result.st.pc)

def Circuit.eval {p : ℕ} (circuit : Circuit p) (varStore : VarStore p) (st : State) (σ : HashConsSt p) : CircuitResult p :=
  Circuit.evalInOrder circuit σ ⟨st, varStore, True⟩

notation "[" varStore ", " σ ", " st "|" circuit "]ₑ" => Circuit.eval circuit varStore st σ

namespace CircuitResult

variable {p pc : ℕ} {σ : HashConsSt p} {constraints constraints1 constraints2 : Prop} {st : State}
         {varStore : VarStore p} {circuit : Circuit p} {e! : ExprRef} {gate : Gate p}
         {result : CircuitResult p}

@[simp, grind =]
lemma pc_step : [result, σ|gate]ₛ.st.pc = result.st.pc + 1 := by aesop (add simp step)

/--
Well formed up to `st.pc`.
-/
@[grind =]
def _root_.Clap.Circuit.wellFormed
  (circuit : Circuit p)
  (st : State)
  (Γ : VarStore p)
  (σ : HashConsSt p) : Prop :=
  circuit.refsValid σ.exprs.size ∧
  circuit.varsAllocated Γ σ st.pc ∧
  st.pc < circuit.size

lemma wellFormed_step (h : circuit.wellFormed st varStore σ) :
  let next := [⟨st, varStore, constraints⟩, σ|circuit[st.pc]'(by grind)]ₛ
  circuit.wellFormed next.st next.varStore σ := by
  by_cases h_sz : circuit.size = 0
  · grind
  · intros next; have eq₁ : next = [⟨st, varStore, constraints⟩, σ|circuit[st.pc]'(by grind)]ₛ := by grind
    set gate := circuit[st.pc]'(by grind) with eq₂
    rcases heq : gate with e | e | e | ⟨w, e⟩
    · simp [heq, bumpPc] at eq₁
      suffices circuit.varsAllocated varStore σ next.st.pc by grind
      unfold Circuit.varsAllocated at h ⊢
      intros i hi
      by_cases eq : i < next.st.pc
      · grind
      · have : i = next.st.pc := by grind
        subst this
        by_cases eq₃ : next.st.pc < circuit.size
        · obtain ⟨gate', h_gate'⟩ : ∃ gate', circuit[next.st.pc]? = .some gate' := by aesop
          rw [h_gate']
          simp
          unfold Gate.varsAllocated
          rcases heq₁ : gate' with e' | e' | e' | ⟨w, e'⟩
          · simp
            
          rw [show circuit[next.st.pc]? = .some gate by grind]
          simp [heq]
          

          
          specialize h st.pc.pred
          sorry 
        · have : next.st.pc = st.pc + 1 := by grind
          simp at eq₃
          rw [this] at eq₃
          done




      · grind  
    done

@[ext, grind ext]
lemma ext {p : ℕ} {r1 r2 : CircuitResult p}
  (h_numAlloc : r1.st = r2.st)
  (h_varStore : r1.varStore = r2.varStore)
  (h_constraints : r1.constraints = r2.constraints)
:
  r1 = r2
:= by
  grind [cases CircuitResult]

lemma foldl_step_numAlloc_independent_of_constraints
:
  (Circuit.evalInOrder circuit σ ⟨st, varStore, constraints1⟩).st =
  (Circuit.evalInOrder circuit σ ⟨st, varStore, constraints2⟩).st
:= by
  rcases circuit with ⟨circuit⟩
  simp only [List.size_toArray, List.foldl_toArray']
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> grind

lemma foldr_step_numAlloc_independent_of_constraints
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints1⟩ circuit).st =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints2⟩ circuit).st
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact foldl_step_numAlloc_independent_of_constraints

lemma foldr_step_numAlloc_independent_of_constraints'
:
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints1⟩ circuit.toList).st =
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints2⟩ circuit.toList).st
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_numAlloc_independent_of_constraints

lemma foldl_step_varStore_independent_of_constraints
:
  (Circuit.evalInOrder circuit σ ⟨st, varStore, constraints1⟩).varStore =
  (Circuit.evalInOrder circuit σ ⟨st, varStore, constraints2⟩).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse
  -- TODO This used to be just `induction <;> grind`, now we need lemmas in terms of `GetElem?`
  -- to push through
  -- TODO you know what, whatever works at this point...
  grind [=GetElem?.getElem?]
  simp
  next hd tl ih =>
    simp at *
    rcases hd with _ | _ | _ | _
    · grind
    · 
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [bumpPc.eq_def, ih]
      rw [foldr_step_numAlloc_independent_of_constraints']
      congr 1
      grind
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      simp [bumpPc.eq_def]
      rw [foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2)]
      grind [GetElem?.getElem?, instGetElemProdExprRefHashConsStZModMem]
    · simp [bumpPc.eq_def]
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2)]
      simp
      rw [ih]
      congr 3
      simp [GetElem?.getElem?, get?]
      rw [ih]

lemma foldr_step_varStore_independent_of_constraints
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints1⟩ circuit).varStore =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints2⟩ circuit).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact foldl_step_varStore_independent_of_constraints

lemma foldr_step_varStore_independent_of_constraints'
:
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints1⟩ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints2⟩ circuit.toList).varStore
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_varStore_independent_of_constraints

@[grind .]
lemma getElem_foldr_independent_of_constraints
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints1⟩ circuit)[(e!, σ)]? =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨st, varStore, constraints2⟩ circuit)[(e!, σ)]?
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  simp [GetElem?.getElem?, get?]
  rw [foldr_step_varStore_independent_of_constraints']

/--
This exists to appease `grind`.

NB this is useless now.
-/
-- @[grind! .] -- I don't think there's an easy way to teach grind about the `σ` under the lambda
lemma foldr_step_varStore_independent_of_constraints''
  {circuit : Circuit p}
  {σ₁ σ₂ : CircuitResult p}
  (h₁ : σ₁.st = σ₂.st)
  (h₂ : σ₁.varStore = σ₂.varStore)
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit).varStore =
  (Array.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit).varStore
:= by
  convert foldr_step_varStore_independent_of_constraints using 4 <;> grind

lemma foldr_step_varStore_independent_of_constraints'''
  {circuit : Circuit p}
  {σ₁ σ₂ : CircuitResult p}
  (h₁ : σ₁.st = σ₂.st)
  (h₂ : σ₁.varStore = σ₂.varStore) :
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit.toList).varStore := by
  simp [Array.foldr_toList]
  apply foldr_step_varStore_independent_of_constraints'' <;> grind

@[simp, grind .]
lemma isSome_foldr_split {result : CircuitResult p} {circuit : Circuit p} {e : ExprRef} :
  (List.foldr (fun x y => [y, σ|x]ₛ) result.split circuit.toList)[(e, σ)]?.isSome ↔
  (List.foldr (fun x y => [y, σ|x]ₛ) result circuit.toList)[(e, σ)]?.isSome := by
  rcases result
  simp [split]
  grind

@[simp, grind .]
lemma isSome_foldr_split' {result : CircuitResult p} {circuit : Circuit p} {e : ExprRef} :
  (Array.foldr (fun x y => [y, σ|x]ₛ) result.split circuit)[(e, σ)]?.isSome ↔
  (Array.foldr (fun x y => [y, σ|x]ₛ) result circuit)[(e, σ)]?.isSome := by
  rcases result
  simp [split]
  grind

lemma foldl_step_constraints_and
  {result : CircuitResult p}
  {circuit : Circuit p}
:
  (Circuit.evalInOrder circuit σ result).constraints = (
    result.constraints ∧
    (Circuit.evalInOrder circuit σ result.split).constraints
  )
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse
  -- TODO This used to be just `induction <;> grind`, now we need lemmas in terms of `GetElem?`
  -- to push through
  grind
  simp
  next hd tl ih =>
    simp at *
    rcases hd with _ | _ | _ | _
    · simp
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [get?, bumpPc.eq_def]
      rw [ih]
      rw [foldr_step_varStore_independent_of_constraints''' (σ₂ := result.split)] <;>
      aesop
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp [bumpPc.eq_def, ih]
      expose_names
      rw [isSome_foldr_split]
      aesop
    · simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      grind [GetElem?.getElem?, instGetElemProdExprRefHashConsStZModMem]
    · simp
      unfold GetElem?.getElem?
      rw [Array.foldr_toList, Array.foldr_toList]
      grind

end CircuitResult

namespace Circuit

variable {p : ℕ} {circuit1 circuit2 : Circuit p} {varStore : VarStore p}
         {st : State} {σ : HashConsSt p}

def seq (circuit₁ circuit₂ : Circuit p)
        (varStore : VarStore p)
        (st : State)
        (σ : HashConsSt p)
: CircuitResult p :=
  let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := eval circuit₁ varStore st σ
  let ⟨numAllocPost, varStorePost, constraintsPost⟩ := eval circuit₂ varStoreMid numAllocMid σ
  ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩

syntax "[" term ", " term ", " term "|" term "; " term "]" : term
macro_rules
  | `(term| [$Γ, $σ, $numAlloc | $c₁; $c₂]) => `(seq $c₁ $c₂ $Γ $numAlloc $σ)

@[app_unexpander seq]
def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $c₁ $c₂ $Γ $numAlloc $σ) =>
    `([$Γ, $numAlloc, $σ | $c₁; $c₂])
  | _ => throw ()

@[simp]
lemma numAlloc_seq :
  [varStore, σ, st | circuit1; circuit2].st =
  let mid := [varStore, σ, st|circuit1]ₑ
  [mid.varStore, σ, mid.st|circuit2]ₑ.st
:= rfl

@[simp]
lemma varStore_seq :
  (Circuit.seq circuit1 circuit2 varStore st σ).varStore =
  let mid := [varStore, σ, st|circuit1]ₑ
  [mid.varStore, σ, mid.st|circuit2]ₑ.varStore
:= rfl

@[simp, grind=]
lemma constraints_seq :
  (Circuit.seq circuit1 circuit2 varStore st σ).constraints =
  let mid := [varStore, σ, st|circuit1]ₑ
  mid.constraints ∧ [mid.varStore, σ, mid.st|circuit2]ₑ.constraints
:= rfl

@[simp, grind =]
lemma eval_append
:
  [varStore, σ, st | circuit1 ++ circuit2]ₑ = seq circuit1 circuit2 varStore st σ
:= by
  simp [eval]
  ext1
  all_goals dsimp [seq]
  . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
  . exact CircuitResult.foldl_step_varStore_independent_of_constraints
  . exact CircuitResult.foldl_step_constraints_and

@[simp high, grind =]
lemma eval_singleton
  {numAlloc}
  {command : Gate p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | #[command]]ₑ =
  [unconstrained[numAlloc][varStore], σ | command]ₛ := by
  simp [eval, CircuitResult.step_unconstrained]

@[simp, grind =]
lemma eval_cons
  {numAlloc}
  {command : Gate p}
  {circuit : Circuit p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | ⟨command :: circuit.toList⟩]ₑ =
  seq #[command] circuit varStore numAlloc σ:= by
  rw [show ⟨command :: circuit.toList⟩ = #[command] ++ circuit by simp]
  exact eval_append

section

variable {numAlloc : ℕ} {varStore : VarStore p} {e: ExprRef} {σ : HashConsSt p}

@[simp, grind =]
lemma eval_empty :
  [varStore, σ, st | #[]]ₑ = unconstrained[st][varStore]
:= by rfl

@[simp, grind =]
lemma eval_empty_collection :
  [varStore, σ, st | ∅]ₑ =
  unconstrained[st][varStore]
:= by rfl

@[simp, grind =]
lemma eval_eq0 :
  [varStore, σ, st | #[.eq0 e]]ₑ =
  unconstrained[st][varStore].step (.eq0 e) σ
:= by simp [eval, CircuitResult.addConstraint_unconstrained]

@[simp, grind =]
lemma eval_share :
  [varStore, σ, st | #[.share e]]ₑ =
  unconstrained[st][varStore].step (.share e) σ
:= by
  simp [eval]

@[simp, grind =]
lemma eval_isZero :
  [varStore, σ, st | #[.isZero e]]ₑ =
  unconstrained[st][varStore].step (.isZero e) σ
:= by
  simp [eval]
  rfl

@[simp, grind =]
lemma eval_num2bits {width : ℕ} :
  [varStore, σ, st | #[.num2bits width e]]ₑ =
  unconstrained[st][varStore].step (.num2bits width e) σ
:= by
  simp [eval]

@[simp, grind =]
lemma seq_cons_nil {cmd : Gate p} {circuit : Circuit p} {varStore} {numAlloc} :
  seq (⟨cmd :: circuit.toList⟩) #[] varStore numAlloc σ =
  seq #[cmd] circuit varStore numAlloc σ := by
  aesop (add simp seq)

@[simp high, grind =]
lemma seq_singleton_nil {cmd : Gate p} {varStore} {numAlloc} :
  seq #[cmd] #[] varStore numAlloc σ =
  [varStore, σ, numAlloc| #[cmd]]ₑ := by
  simp [seq]

end

-- TODO prove for eval
-- TODO move up
lemma step_of_refsValid_prefix
  {σ σ' : HashConsSt p}
  {circuit : Gate p}
  {result: CircuitResult p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_refsValid : circuit.refsValid (σ.exprs.size))
:
  [result, σ'|circuit]ₛ =
  [result, σ|circuit]ₛ
:= by
  unfold CircuitResult.step
  cases circuit
  all_goals {
    simp
    expose_names
    have : e < σ.exprs.size := by
      unfold Gate.refsValid at h_refsValid
      grind
    have : result[(e, σ')]? = result[(e, σ)]? := by
      unfold_projs
      simp [CircuitResult.get?, HashConsM.eval]
      congr 1
      symm
      exact HashConsM.evalCache_of_lt_prefix h_prefix this
    grind
  }

@[simp, grind _=_]
lemma refsValid_append_iff {a b : Circuit p} {numAlloc : ℕ}
:
  (a ++ b).refsValid numAlloc ↔
  a.refsValid numAlloc ∧ b.refsValid numAlloc
:= by
  grind

end Clap.Edsl.Circuit
