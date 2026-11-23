import Clap.Model.ConstraintSystem.toCs

/-!
# The variable remap before the slot table (reference)

`offsetSince`, `privateAllocsRef` and `offsetIdxRef` are `offsetSince`, `privateAllocs` and `offsetIdx` verbatim but for the names, and
`offsetHashConsStateRef` is `offsetHashConsState` -/

namespace Clap.ConstraintSystem

def offsetSince (threshold idx offset : ℕ) : ℕ :=
  if idx < threshold then idx else idx + offset

/--
Not to be confused with Colonel Allocs.
-/
def privateAllocsRef (gate : Gate) : ℕ :=
  match gate with
  | .eq0 _ => 0
  | .share _ => 0
  | .isZero _ => 1
  | .num2bits .. => 0
  | .fpmul w k .. =>
    -- `rangeCheckInputs #[] numAlloc width a b p'`
    3 * k * w +
    -- `polyMult constraints numAlloc a b`
    k +
    -- `allocRangeChecked constraints numAlloc k width` (for `q`)
    k * w + k +
    -- PUBLIC: `allocRangeChecked constraints numAlloc k width` (for `r`) (I think; TODO)
    -- k * w + k +
    0 +
    -- `allocUnchecked numAlloc (2 * k - 1)`
    k +
    -- `inner constraints ab t p' q r`
    0 +
    -- `check_carry_zero constraints numAlloc width t`
    (if k == 0 then 0 else k - 1) +
    -- `check_lt constraints numAlloc width r p'`
    k * (w + 2)
    -- TODO replace with subtraction of circuit step numAlloc from cs numalloc

def offsetIdxRef (circuit : Circuit) : ℕ → ℕ :=
  (·.1) <| circuit.foldr (init := (id, circuit.numAllocStep))
    fun gate (f, threshold) ↦
      let privateAllocs := privateAllocsRef gate
      let publicAllocs := gate.numAllocStep
      /-
        [public₁, public₂]
                         ^ threshold
        ^ threshold - publicAllocs
        [priv₁, priv₂, public₁, public₂]
      -/
      let nextThreshold := threshold - publicAllocs
      -- dbg_trace s!"t: {threshold}\npriv: {privateAllocs}\npublic: {publicAllocs}\nnextT: {nextThreshold}"
      let yourFace := fun idx ↦ offsetSince nextThreshold (f idx) privateAllocs
      -- dbg_trace s!"{List.range 50 |>.map yourFace}"
      (yourFace, nextThreshold)

/-- One gate of `offsetIdxRef`: the closure for the gates after it is `acc.1`, and `acc.2` the
first variable after its outputs. -/
def offsetStepRef (gate : Gate) (acc : (ℕ → ℕ) × ℕ) : (ℕ → ℕ) × ℕ :=
  let f := acc.1
  let threshold := acc.2
  let privateAllocs := privateAllocsRef gate
  let publicAllocs := gate.numAllocStep
  /-
    [public₁, public₂]
                     ^ threshold
    ^ threshold - publicAllocs
    [priv₁, priv₂, public₁, public₂]
  -/
  let nextThreshold := threshold - publicAllocs
  let yourFace := fun idx ↦ offsetSince nextThreshold (f idx) privateAllocs
  (yourFace, nextThreshold)

theorem offsetIdxRef_eq_foldr (circuit : Circuit) :
    offsetIdxRef circuit = (circuit.foldr offsetStepRef (id, circuit.numAllocStep)).1 :=
  rfl

def offsetHashConsStateRef {p : ℕ} (numPublicInputs : ℕ) (σ : HashConsSt p) (circuit : Circuit) :
    HashConsSt p :=
  remapVars (offsetIdxRef circuit) numPublicInputs σ

/-! ### The slot table agrees with the previous remap without fpmul -/

section Equivalence

/-- `slotTable` on a list of gates. -/
def slotsSpec : List Gate → List ℕ × ℕ
  | [] => ([], 0)
  | g :: l =>
    (List.range' (outputOffset g) g.numAllocStep ++ (slotsSpec l).1.map (gateSlots g + ·),
      gateSlots g + (slotsSpec l).2)

theorem pushRange_eq (table : Array ℕ) (start n : ℕ) :
    pushRange table start n = table ++ (List.range' start n).toArray := by
  induction n generalizing table start with
  | zero => simp [pushRange]
  | succ n ih =>
    apply Array.toList_inj.mp
    simp [pushRange, ih, List.range'_succ]

theorem slotTable_go_eq (circuit : Circuit) (i : ℕ) (table : Array ℕ) (base : ℕ) :
    slotTable.go circuit i table base =
      (table ++ ((slotsSpec (circuit.toList.drop i)).1.map (base + ·)).toArray,
        base + (slotsSpec (circuit.toList.drop i)).2) := by
  fun_induction slotTable.go circuit i table base with
  | case1 i table base h gate ih =>
    have hd : circuit.toList.drop i = circuit[i] :: circuit.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]
      simp
    rw [ih, hd]
    simp only [slotsSpec, pushRange_eq, gate, Prod.mk.injEq]
    constructor
    · apply Array.toList_inj.mp
      simp [List.map_add_range', Function.comp_def, Nat.add_assoc]
    · omega
  | case2 i table base h =>
    rw [List.drop_eq_nil_of_le (by simpa using h)]
    simp [slotsSpec]

theorem slotTable_eq (circuit : Circuit) :
    slotTable circuit = ((slotsSpec circuit.toList).1.toArray, (slotsSpec circuit.toList).2) := by
  simp [slotTable, slotTable_go_eq]

theorem offsetIdx_cons (g : Gate) (l : List Gate) (i : ℕ) :
    offsetIdx ⟨g :: l⟩ i =
      if i < g.numAllocStep then outputOffset g + i
      else gateSlots g + offsetIdx ⟨l⟩ (i - g.numAllocStep) := by
  simp only [offsetIdx, slotOf, slotTable_eq, slotsSpec, List.size_toArray, List.length_append,
    List.length_range', List.length_map, List.getElem?_toArray]
  split
  · rename_i hi
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hi]
  · rename_i hi
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_range', List.getElem?_map]
    cases hT : (slotsSpec l).1[i - g.numAllocStep]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hT
      simp only [Option.map_none, Option.getD_none]
      omega
    | some v => simp

theorem offsetStepRef_snd (l : List Gate) (t : ℕ) :
    (l.foldr offsetStepRef (id, t)).2 = t - (l.map Gate.numAllocStep).sum := by
  induction l with
  | nil => simp
  | cons g l ih => simp [offsetStepRef, ih, Nat.sub_sub, Nat.add_comm]

theorem offsetStepRef_fst (l : List Gate) (s i : ℕ) :
    (l.foldr offsetStepRef (id, s + (l.map Gate.numAllocStep).sum)).1 i =
      if i < s then i
      else s + (l.foldr offsetStepRef (id, (l.map Gate.numAllocStep).sum)).1 (i - s) := by
  induction l generalizing s i with
  | nil => simp; omega
  | cons g l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [show s + (g.numAllocStep + (l.map Gate.numAllocStep).sum) =
      (s + g.numAllocStep) + (l.map Gate.numAllocStep).sum by omega]
    simp only [offsetStepRef, offsetStepRef_snd, ih, offsetSince, Nat.add_sub_cancel,
      Nat.sub_self, Nat.sub_sub]
    split_ifs <;> omega

theorem offsetIdxRef_cons (g : Gate) (l : List Gate) (i : ℕ) :
    offsetIdxRef ⟨g :: l⟩ i =
      (if i < g.numAllocStep then i
        else g.numAllocStep + offsetIdxRef ⟨l⟩ (i - g.numAllocStep)) + privateAllocsRef g := by
  have hsum (l : List Gate) : Circuit.numAllocStep ⟨l⟩ = (l.map Gate.numAllocStep).sum := by
    simp [Circuit.numAllocStep]
  have hfold (l : List Gate) (t : ℕ) :
      (⟨l⟩ : Circuit).foldr offsetStepRef (id, t) = l.foldr offsetStepRef (id, t) := by
    rw [← Array.foldr_toList]
  simp only [offsetIdxRef_eq_foldr, hsum, hfold, List.foldr_cons, List.map_cons, List.sum_cons]
  simp only [offsetStepRef, offsetStepRef_snd, offsetStepRef_fst, offsetSince, Nat.add_sub_cancel,
    Nat.sub_self, Nat.not_lt_zero, if_false]

/-- On a circuit without fpmul, the slot table is the previous remap. -/
theorem offsetIdx_eq_offsetIdxRef (circuit : Circuit)
    (h : ∀ gate ∈ circuit, (gate matches .fpmul ..) = false) :
    offsetIdx circuit = offsetIdxRef circuit := by
  obtain ⟨l⟩ := circuit
  induction l with
  | nil =>
    funext i
    simp [offsetIdx, slotOf, slotTable_eq, slotsSpec, offsetIdxRef_eq_foldr, Circuit.numAllocStep]
  | cons g l ih =>
    have hl := ih (fun gate hm ↦ h gate (by simp at hm ⊢; exact .inr hm))
    have hg := h g (by simp)
    funext i
    rw [offsetIdx_cons, offsetIdxRef_cons, hl]
    cases g <;> simp_all [outputOffset, gateSlots, privateAllocsRef, Gate.numAllocStep,
      share.numAllocStep, isZero.numAllocStep, num2bits.numAllocStep, eq0.numAllocStep]
    -- isZero: its output is after its private inverse
    split <;> omega

theorem offsetHashConsState_eq_offsetHashConsStateRef {p : ℕ} (numInputs : ℕ) (σ : HashConsSt p)
    (circuit : Circuit) (h : ∀ gate ∈ circuit, (gate matches .fpmul ..) = false) :
    offsetHashConsState numInputs σ circuit = offsetHashConsStateRef numInputs σ circuit := by
  show remapVars (offsetIdx circuit) numInputs σ = remapVars (offsetIdxRef circuit) numInputs σ
  rw [offsetIdx_eq_offsetIdxRef circuit h]

end Equivalence

end Clap.ConstraintSystem
