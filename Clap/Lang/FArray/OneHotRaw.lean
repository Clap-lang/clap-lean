import Clap.Lang.F.eq

namespace Clap.Edsl.Lang.FArray

variable {p : ℕ}

def oneHotRaw [p.AtLeastTwo] (len : ℕ) (idx : F p) : Edsl.CircuitStateM p (Vector (FB p) len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ F.eq idx i)

namespace oneHotRaw

def runAndEval
  {p : ℕ} {ResultT : Type} (cmd : CircuitStateM p ResultT) (numAlloc : ℕ) (varStore : Std.ExtTreeMap ℕ (ZMod p))
:
  ResultT × CircuitResult p
:=
  let ⟨⟨result, circuit⟩, _numAlloc⟩ := (cmd.run numAlloc)
  ⟨result, Edsl.CircuitState.eval circuit varStore numAlloc⟩


-- def matchesUnaryBitVecFunctionWithSideEffects
--   {length: ℕ}
--   (p : ℕ)
--   [p.AtLeastTwo]
--   (spec_function : (ZMod p) → Vector Bool length)
--   (function : (F p) → Edsl.CircuitStateM p (Vector (FB p) length))
--   (allocates : ℕ)
-- : Prop :=
--   ∀ (a : F p) varStorePre numAllocPre,
--   a.isValid (varStorePre.get?) →
--   let a_eval := (a.eval varStorePre.get?).getD 0
--   let ⟨result, numAllocPost, varStorePost, constraints⟩ := runAndEval (function a) numAllocPre varStorePre
--   result.map (FB.toBool · varStorePost.get?) = spec_function a_eval ∧
--   constraints = True ∧
--   numAllocPost = numAllocPre + allocates ∧
--   ∀ i < numAllocPre, varStorePost.get? i = varStorePre.get? i ∧
--   ∀ (i: Fin length),
--     varStorePost.get? (numAllocPost - i) =
--     .some (((spec_function a_eval).get ⟨length - 1 - i, by {
--       omega
--     }⟩).toNat)

def specFunction (n : ℕ) : Fin n → Vector Bool n := fun i ↦
  Vector.ofFn λ (idx : Fin n) => idx.val == i

def isValidRange (varStore : VarStore p) (x : F p) (lt : ℕ) : Prop :=
  (x.eval varStore).any (λ val => val.val < lt)

lemma eval_of_isValidRange
  {varStore : VarStore p}
  {x : F p}
  {lt : ℕ}
  (h: isValidRange varStore x lt)
:
  ∃ val, x.eval varStore = .some val ∧ val.val < lt
:= by
  unfold isValidRange at h
  grind [Option.any_eq_true]

-- TODO there must surely be a better name for this
-- DONE Yes, it's this name.
lemma val_get_eval_mod_lt
  {varStore : VarStore p}
  {k : ℕ}
  {x : F p}
  {h : (FixedExp.eval varStore x).isSome = true}
  [Fact (k ≤ p)]
  (h_isValid : isValidRange varStore x k)
:
  ((x.eval varStore).get h).val % p < k
:= by
  apply Nat.mod_lt_of_lt
  grind [eval_of_isValidRange]

attribute [local grind _=_] Array.toList_mapM Vector.toArray_mapM
attribute [local grind =] Vector.map_id_fun Vector.map_id ZMod.val_natCast
attribute [local grind .] Vector.mem_toArray_iff

instance {k p} [inst_lt : Fact (k ≤ p)] : FB.Convert p (F p) (Fin k) where
  isValid varStore x :=
    isValidRange varStore x k
  size :=
    1
  toLinear varStore x :=
    #v[x.eval varStore |>.getD 42]
  toIdeal varStore x :=
    (x.eval varStore).bind (λ x => if h: x.val < k then .some ⟨x.val, h⟩ else .none)
  toRepresents x :=
    x.val
  someOfIsValid varStore x h_isValid := by
    grind [eval_of_isValidRange]
  toIdealtoRepresents varStore x := by
    simp [Nat.mod_eq_of_lt (lt_of_lt_of_le x.2 inst_lt.out)]
  toRepresentstoIdeal varStore x h_isValidRange:= by
    obtain ⟨x, ⟨h_some, h_range⟩⟩ := eval_of_isValidRange h_isValidRange
    have : x.val % p = x.val := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_range inst_lt.out)
    grind

@[grind _=_]
lemma _root_.Vector.isSome_mapM_eq_all_isSome
  {elemT resultT}
  {length}
  {f : elemT → Option resultT}
  {xs : Vector elemT length}
:
  (Vector.mapM f xs).isSome =
  (xs.map f).all Option.isSome
:= by
  have :
    (Vector.mapM f xs).isSome =
    (Vector.toArray <$> (Vector.mapM f xs)).isSome
  := by grind
  rewrite [this]; clear this
  simp
  rewrite [Array.mapM_eq_mapM_toList]
  have :
    xs.toArray.toList = xs.toList
  := rfl
  rewrite [this]; clear this
  have :
    (xs.all λ a => (f a).isSome) =
    xs.toList.all fun a => (f a).isSome
  := by
    rw [←Vector.all_toList]
  rewrite [this]; clear this
  induction xs.toList with
  | nil => simp
  | cons head tail h_tail =>
    simp
    cases (f head) with
    | none => simp
    | some head =>
      rewrite [←h_tail]
      simp
      cases (List.mapM f tail) with
      | none => grind
      | some rest => grind

@[grind =_]
lemma toIdeal_eq_pure_get_of_isValid
  {representsT idealT}
  {varStore : VarStore p}
  {x : representsT}
  [FB.Convert p representsT idealT]
  (h : FB.IsValid.isValid varStore x)
:
  FB.Convert.toIdeal varStore x =
  pure ((FB.Convert.toIdeal varStore x).get (FB.Convert.someOfIsValid varStore x h))
:= by
  simp

@[grind =]
lemma _root_.List.mapM_toRepresentstoIdeal
  {representsT idealT}
  {varStore : VarStore p}
  {xs : List representsT}
  [base : FB.Convert p representsT idealT]
  {h}
:
  List.mapM (base.toIdeal varStore ∘ base.toRepresents)
    ((List.mapM (FB.Convert.toIdeal varStore) xs).get h) =
  List.mapM (FB.Convert.toIdeal varStore) xs
:= by
  induction xs with
  | nil => simp
  | cons head tail h_tail =>
    simp [h_tail, base.toIdealtoRepresents]

@[grind .]
lemma _root_.List.isSome_mapM_of_isSome
  {T T'}
  {list : List T}
  {f : T → Option T'}
  (h : ∀ x ∈ list, (f x).isSome)
:
  (List.mapM f list).isSome
:= by
  induction list with
  | nil => simp
  | cons head tail h_tail =>
    have h_head := h head (by simp)
    obtain ⟨head, h_head⟩ := Option.isSome_iff_exists.mp h_head
    simp [h_head]
    simp_all -- forgive me
    obtain ⟨tail, h_tail⟩ := Option.isSome_iff_exists.mp h_tail
    simp [h_tail]

instance
  {representsT idealT length}
  [base: FB.Convert p representsT idealT]
: FB.Convert p (Vector representsT length) (Vector idealT length) where
  isValid varStore xs :=
    ∀ x ∈ xs, base.isValid varStore x
  size := length * base.size
  toLinear varStore xs :=
    xs.flatMap (base.toLinear varStore)
  toIdeal varStore xs :=
    let ideals := xs.map (base.toIdeal varStore)
    ideals.mapM id
  toRepresents xs :=
    xs.map base.toRepresents
  someOfIsValid varStore x h_isValid := by
    grind
  toIdealtoRepresents varStore xs := by
    simp only [Function.comp_def, Vector.mapM_map]
    have := Vector.mapM_pure (m := Option) (xs := xs) (id : idealT → idealT)
    grind
  toRepresentstoIdeal varStore xs h := by
    simp
    rewrite [←Vector.map_toArray_inj, ←Array.map_toList_inj]
    simp
    have (h : (Vector.mapM (FB.Convert.toIdeal varStore) xs).isSome) (h') :
      ((Vector.mapM (base.toIdeal varStore) xs).get h).toArray.toList =
      (Array.toList <$> Vector.toArray <$> (Vector.mapM (base.toIdeal varStore) xs)).get h'
    := by
      grind
    grind

def spec (p : ℕ) (length : ℕ) [p.AtLeastTwo] [Fact (length ≤ p)] : Prop :=
  Clap.Edsl.Lang.FB.matchesUnaryMonadFunction
  p
  (specFunction length)
  (oneHotRaw length)
  length

lemma equiv (p : ℕ) (length : ℕ) [p.AtLeastTwo] :
  spec p length
:= by
  unfold spec
  intro a varStorePre numAllocPre h_a_isValid
  obtain ⟨a_eval, h_a_eval⟩ := Option.isSome_iff_exists.mp h_a_isValid
  aesop (add simp [
    Clap.monads,
    oneHotRaw,
    F.eq.equiv
  ]) (add safe (by grind))

end oneHotRaw

end Clap.Edsl.Lang.FArray
