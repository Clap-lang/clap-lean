import Clap.Lang.F.F
import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.F

variable {p : ℕ}

open Convert Edsl in
/-- Monadic value-returning refinement predicate that decodes the returned value against the
    post-run store, unlike the generic `matchesUnaryMonadFunction` whose first two conjuncts
    decode `getResult` against `varStorePre` (where a freshly-allocated result is always empty) -/
def matchesUnaryMonadFunctionPost (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → CircuitStateM p funOut)
  (allocatesN : ℕ)
  (constraints : specIn → Prop)
: Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p) (numAllocPre : ℕ),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h)
      let ⟨result, circuit⟩ : funOut × CircuitResult p :=
        CircuitStateM.runAndEval (function a) numAllocPre varStorePre
      circuit.constraints = (constraints aVal) ∧
      circuit.numAlloc = numAllocPre + allocatesN ∧
      (∀ n < numAllocPre, circuit.varStore[n]? = varStorePre[n]?) ∧
      -- result decoded against the POST-run store equals the spec value (this replaces
      -- matchesUnaryMonadFunction's two broken pre-store conjuncts):
      toIdeal circuit.varStore result = .some (spec_function aVal)

open Convert in
/-- Pure unary refinement predicate that takes input validity as a hypothesis (the unary
    analogue of `matchesBinaryFunction`'s body). Unlike `matchesUnaryFunction`, it does NOT assert a
    validity-iff, which is false whenever the input's validity domain is strictly narrower than the
    output's -/
def matchesUnaryFunctionOfValid (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → funOut)
: Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h)
      letI resultVal : Option specOut := toIdeal varStorePre (function a)
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      resultVal = toIdeal varStorePre wrapped

/-- LSB-first bit decomposition of `e` into `w` fresh `FB p` variables -/
def num2bits [p.AtLeastTwo] (w : ℕ) (e : F p) : Edsl.CircuitStateM p (Vector (FB p) w) :=
  Edsl.num2bits w e

namespace num2bits

private lemma num2bitsLsbPureV_aux_toList {w : ℕ} (v : ZMod p) :
    (num2bitsLsbPureV.aux w v).toList = (num2bitsLsbPure w v).reverse := by
  induction w generalizing v with
  | zero => simp [num2bitsLsbPureV.aux, num2bitsLsbPure]
  | succ w ih =>
    simp only [num2bitsLsbPureV.aux, num2bitsLsbPure, Vector.toList_push, List.reverse_cons, ih]

private lemma num2bitsLsbPureV_toList (w : ℕ) (v : ZMod p) :
    (num2bitsLsbPureV w v).toList = num2bitsLsbPure w v := by
  simp [num2bitsLsbPureV, Vector.toList_reverse, num2bitsLsbPureV_aux_toList]

private lemma num2bitsLsbPure_getElem_val [NeZero p] (f : ZMod p) (n i : ℕ) (hi : i < n) :
    (num2bitsLsbPure n f)[i]'(num2bitsLsbPure_length ▸ hi) =
    ((f.val / 2 ^ i % 2 : ℕ) : ZMod p) := by
  induction n generalizing f i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [num2bitsLsbPure]
    cases i with
    | zero => simp
    | succ i' =>
      have hi' : i' < n := Nat.lt_of_succ_lt_succ hi
      simp only [List.getElem_cons_succ]
      have hrem : ((f.val / 2 : ℕ) : ZMod p).val = f.val / 2 :=
        ZMod.val_cast_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (ZMod.val_lt f))
      rw [ih ((f.val / 2 : ℕ) : ZMod p) i' hi', hrem, pow_succ,
          show 2 ^ i' * 2 = 2 * 2 ^ i' from mul_comm _ _, ← Nat.div_div_eq_div_mul]

private lemma num2bitsLsbPureV_getElem_val [NeZero p] (f : ZMod p) (w i : ℕ) (hi : i < w) :
    (num2bitsLsbPureV w f)[i]'hi = ((f.val / 2 ^ i % 2 : ℕ) : ZMod p) := by
  have hval := num2bitsLsbPureV_toList w f
  have hlen : i < (num2bitsLsbPureV w f).toList.length := Vector.length_toList ▸ hi
  calc (num2bitsLsbPureV w f)[i]'hi
      = (num2bitsLsbPureV w f).toList[i]'hlen := (Vector.getElem_toList hlen).symm
    _ = (num2bitsLsbPure w f)[i]'(hval ▸ hlen) := List.getElem_of_eq hval hlen
    _ = ((f.val / 2 ^ i % 2 : ℕ) : ZMod p) := num2bitsLsbPure_getElem_val f w i hi

private lemma num2bitsLsbPureV_getElem_testBit [NeZero p] (f : ZMod p) (w i : ℕ) (hi : i < w) :
    (num2bitsLsbPureV w f)[i]'hi = if f.val.testBit i then (1 : ZMod p) else 0 := by
  rw [num2bitsLsbPureV_getElem_val f w i hi, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (f.val / 2 ^ i) with h | h <;> simp [h]

/-- bit `i` of the output is bit `i` of `e`'s value (`Nat.testBit`) -/
def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  matchesUnaryMonadFunctionPost p
    (spec_function := fun (v : ZMod p) => Vector.ofFn (fun i : Fin w => v.val.testBit i))
    (function := num2bits w)
    (allocatesN := w)
    (constraints := fun (_ : ZMod p) => True)

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by
  unfold spec matchesUnaryMonadFunctionPost num2bits
  intro a varStorePre numAllocPre h
  obtain ⟨aVal, hAVal⟩ := Option.isSome_iff_exists.mp h
  rw [CircuitStateM.runAndEval_eq]
  rw [CircuitState.eval_edsl_num2bits, CircuitState.eval_num2bits, CircuitResult.step_num2bits]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [CircuitResult.assertAllocated_unconstrained, CircuitResult.addConstraint_unconstrained,
      CircuitResult.get?_unconstrained, Membership.mem, hAVal]
  · simp
  · intro n hn
    simp only [CircuitResult.varStore_alloc, CircuitResult.numAlloc_assertAllocated,
      CircuitResult.varStore_assertAllocated, CircuitResult.varStore_unconstrained,
      CircuitResult.numAlloc_unconstrained]
    exact VarStore.getElem?_insertMany_alloc_of_lt _ hn
  · have hvs : (((unconstrained[numAllocPre][varStorePre]).assertAllocated a).alloc
        (num2bitsLsbPureV w (unconstrained[numAllocPre][varStorePre])[a]!)).varStore
      = varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip (num2bitsLsbPureV w aVal)) := by
      simp [CircuitResult.varStore_alloc,
        CircuitResult.varStore_unconstrained, CircuitResult.get?_unconstrained,
        GetElem?.getElem!, hAVal]
    simp only [F.toIdeal_def, hAVal, Option.get_some]
    rw [hvs]
    show (((Edsl.num2bits w a).getResult numAllocPre).map
        (fun x => Convert.toIdeal
          (varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip (num2bitsLsbPureV w aVal))) x)
      ).mapM id
      = some (Vector.ofFn (fun i : Fin w => aVal.val.testBit i))
    have hmap : ((Edsl.num2bits w a).getResult numAllocPre).map
        (fun x => Convert.toIdeal
          (varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip (num2bitsLsbPureV w aVal))) x)
      = (Vector.ofFn (fun i : Fin w => aVal.val.testBit i)).map some := by
      apply Vector.toList_inj.mp
      rw [Vector.toList_map, Vector.toList_map]
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_map, List.getElem?_map, Vector.getElem?_toList, Vector.getElem?_toList,
        Vector.getElem?_ofFn]
      by_cases hi : i < w
      · simp only [hi, dif_pos, Option.map_some]
        have hr := getResult_num2bits_getElem? (width := w) (numAlloc := numAllocPre) (e := a) hi
        have hv : (varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip
              (num2bitsLsbPureV w aVal)) : VarStore p)[numAllocPre + i]?
            = some (num2bitsLsbPureV w aVal)[i] :=
          VarStore.getElem?_insertMany_alloc_of_lt' varStorePre hi
        rw [hr, Option.map_some, FB.toIdeal_eq]
        show some (FB.toBool (Exp.v (numAllocPre + i))
            (varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip
              (num2bitsLsbPureV w aVal)) : VarStore p))
          = some (some (aVal.val.testBit i))
        congr 1
        unfold FB.toBool
        rw [FixedExp.eval_v]
        refine (congrArg (fun o => Option.bind o
          (fun x => if x == 1 then some true else if x == 0 then some false else none)) hv).trans ?_
        rw [Option.bind_some, num2bitsLsbPureV_getElem_testBit aVal w i hi]
        by_cases htb : aVal.val.testBit i <;> simp [htb]
      · simp [hi]
    rw [hmap, Vector.mapM_map]
    show (Vector.ofFn (fun i : Fin w => aVal.val.testBit i)).mapM some
      = some (Vector.ofFn (fun i : Fin w => aVal.val.testBit i))
    simpa using Vector.mapM_pure (m := Option) (xs := Vector.ofFn (fun i : Fin w => aVal.val.testBit i)) id

/-- Single-bit companion to `equiv`'s whole-vector decode: the `i`-th entry of `num2bits`'s
    result, read back against the post-run store, is bit `i` of `a`'s value. Needed by circuits
    (like `F.lessThan`) that call `num2bits` as a sub-expression and only need one bit, not the
    whole vector — no generic "extract one element from a whole-vector `toIdeal`" lemma exists
    to un-project `equiv`'s conclusion, so this repeats `equiv`'s own per-index argument directly. -/
lemma toIdeal_getElem [p.AtLeastTwo] [NeZero p] {a : F p} {varStorePre : VarStore p} {aVal : ZMod p}
    (hAVal : a.toZMod varStorePre = .some aVal) (numAllocPre w i : ℕ) (hi : i < w) :
  Convert.toIdeal (CircuitStateM.runAndEval (num2bits w a) numAllocPre varStorePre).2.varStore
    ((CircuitStateM.runAndEval (num2bits w a) numAllocPre varStorePre).1[i]'hi) =
  .some (aVal.val.testBit i)
:= by
  simp only [CircuitStateM.runAndEval_eq]
  unfold num2bits
  rw [CircuitState.eval_edsl_num2bits, CircuitState.eval_num2bits, CircuitResult.step_num2bits]
  rw [F.toZMod_def] at hAVal
  have hvs : (((unconstrained[numAllocPre][varStorePre]).assertAllocated a).alloc
      (num2bitsLsbPureV w (unconstrained[numAllocPre][varStorePre])[a]!)).varStore
    = varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip (num2bitsLsbPureV w aVal)) := by
    simp [CircuitResult.varStore_alloc, CircuitResult.varStore_unconstrained,
      CircuitResult.get?_unconstrained, GetElem?.getElem!, hAVal]
  rw [hvs]
  have hr := getResult_num2bits_getElem? (width := w) (numAlloc := numAllocPre) (e := a) hi
  have hv : (varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip
        (num2bitsLsbPureV w aVal)) : VarStore p)[numAllocPre + i]?
      = some (num2bitsLsbPureV w aVal)[i] :=
    VarStore.getElem?_insertMany_alloc_of_lt' varStorePre hi
  have hgetElem : ((Edsl.num2bits w a).getResult numAllocPre)[i]'hi = Exp.v (numAllocPre + i) := by
    have h' := hr
    rw [Vector.getElem?_eq_getElem hi] at h'
    exact Option.some.inj h'
  rw [FB.toIdeal_eq]
  show FB.toBool (((Edsl.num2bits w a).getResult numAllocPre)[i]'hi)
      (varStorePre.insertMany ((Vector.range w).map (·+numAllocPre) |>.zip (num2bitsLsbPureV w aVal)))
    = some (aVal.val.testBit i)
  rw [hgetElem]
  unfold FB.toBool
  rw [FixedExp.eval_v]
  refine (congrArg (fun o => Option.bind o
    (fun x => if x == 1 then some true else if x == 0 then some false else none)) hv).trans ?_
  rw [Option.bind_some, num2bitsLsbPureV_getElem_testBit aVal w i hi]
  by_cases htb : aVal.val.testBit i <;> simp [htb]

end num2bits

def bits2num {w : ℕ} (bits : Vector (FB p) w) : F p :=
  Vector.foldr (fun b acc => b + 2 * acc) 0 bits

namespace bits2num

def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  matchesUnaryFunctionOfValid p
    (spec_function := fun (bits : Vector Bool w) =>
      (∑ i : Fin w, if bits[i] then (2 : ZMod p) ^ i.1 else 0))
    (function := bits2num (p := p) (w := w))

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by sorry

end bits2num

end Clap.Edsl.Lang.F
