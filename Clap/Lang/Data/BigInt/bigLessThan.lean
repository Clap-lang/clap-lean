import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.or
import Clap.Util.Limbs

/-!
# comparing two bignums

Circom: `BigLessThan(n, k)`.-/

namespace Clap.Lang.BigInt

variable {p : ℕ}

namespace bigLessThan

/-- Limb `i`'s comparison bits `(lt[i], eq[i])`. -/
def ltEq [p.AtLeastTwo] (n : ℕ) (xy : F p × F p) : ClapM p (FArray p 2) := do
  -- Circom: lt[i] = LessThan(n); lt[i].in[0] <== a[i]; lt[i].in[1] <== b[i];
  let lt ← lessThan n xy.1 xy.2
  -- Circom: eq[i] = IsEqual(); eq[i].in[0] <== a[i]; eq[i].in[1] <== b[i];
  let e ← eq xy.1 xy.2
  pure #v[lt, e]

/-- One step of the chain, from `acc = (ors[i + 1], eq_ands[i + 1])` and `le = (lt[i], eq[i])`. -/
def chainStep [p.AtLeastTwo] (acc le : FArray p 2) : ClapM p (FArray p 2) := do
  -- Circom: ands[i].a <== eq_ands[i + 1].out; ands[i].b <== lt[i].out;
  let and ← FB.and acc[1] le[0]
  -- Circom: eq_ands[i].a <== eq_ands[i + 1].out; eq_ands[i].b <== eq[i].out;
  let eqAnd ← FB.and acc[1] le[1]
  -- Circom: ors[i].a <== ors[i + 1].out; ors[i].b <== ands[i].out;
  let or ← FB.or acc[0] and
  pure #v[or, eqAnd]

end bigLessThan

def bigLessThan [p.AtLeastTwo] (n : ℕ) {k : ℕ} (a b : FVec p (k + 1)) : ClapM p (FB p) := do
  -- Circom: for (var i = 0; i < k; i++) { lt[i] … ; eq[i] … }
  let ltEq ← (a.zip b).mapM (bigLessThan.ltEq n)
  -- Circom: for (var i = k - 2; i >= 0; i--) { ands[i] … ; eq_ands[i] … ; ors[i] … }, where the
  -- Circom: first iteration reads ors[i + 1] = lt[k - 1] and eq_ands[i + 1] = eq[k - 1].
  let acc ← ltEq.pop.reverse.foldlM bigLessThan.chainStep ltEq[k]
  -- Circom: out <== ors[0].out;
  return acc[0]

namespace bigLessThan

/-- One step of the chain: `acc = (ors, eq_ands)` above limb `i`, `le = (lt[i], eq[i])`. -/
def stepSpec (acc le : Vector Bool 2) : Vector Bool 2 :=
  #v[acc[0] || (acc[1] && le[0]), acc[1] && le[1]]

/-- The per-limb bits `(lt[i], eq[i])` for any inputs. -/
def ltEqRaw (n : ℕ) (xy : ZMod p × ZMod p) : Vector Bool 2 :=
  #v[lessThan.lessThanRaw n xy.1 xy.2, xy.1 == xy.2]

/-- What `bigLessThan n` computes for any inputs. -/
def raw (n : ℕ) {k : ℕ} (a_vals b_vals : Vector (ZMod p) (k + 1)) : Bool :=
  let ltEq := (a_vals.zip b_vals).map (ltEqRaw n)
  (ltEq.pop.reverse.foldl stepSpec ltEq[k])[0]

/-- Element `i` of a converting vector of bit vectors converts to element `i` of its values: the
projection out of `Conversion.vector` that the chain needs, through `FArray.converts_flatten`. -/
private lemma converts_getElem_of_vector
  {k w i : ℕ}
  {state : ClapMState p}
  {exprs : Vector (FArray p w) k}
  {vals : Vector (Vector Bool w) k}
  (h : Converts (Conversion.vector FArray.conversion k) state exprs vals)
  (h_i : i < k)
:
  Converts FArray.conversion state exprs[i] vals[i]
:= by
  have h_flat := FArray.converts_iff_FB_converts.mp (FArray.converts_flatten h)
  rw [FArray.converts_iff_FB_converts]
  intro ⟨j, h_j⟩
  have h_idx : i * w + j < k * w := by nlinarith
  have := h_flat ⟨i * w + j, h_idx⟩
  simp only [Fin.getElem_fin, Vector.getElem_flatten] at this
  have h_div : (i * w + j) / w = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h_j, zero_add]
  have h_mod : (i * w + j) % w = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_j]
  simpa [h_div, h_mod] using this

private lemma converts_pair {state : ClapMState p} {x y : FB p} {x_val y_val : Bool}
  (h_x : Converts FB.conversion state x x_val) (h_y : Converts FB.conversion state y y_val) :
  Converts FArray.conversion state #v[x, y] #v[x_val, y_val]
:= by
  rw [FArray.converts_iff_FB_converts]
  intro ⟨i, h_i⟩
  match i, h_i with
  | 0, _ => simpa using h_x
  | 1, _ => simpa using h_y

private lemma ltEq_convertsM [p.AtLeastTwo] {n : ℕ}
  {state : ClapMState p} {xy : F p × F p} {xy_val : ZMod p × ZMod p}
  (h : Converts FPair.conversion state xy xy_val)
:
  ConvertsM FArray.conversion (ltEq n xy) state (ltEqRaw n xy_val)
    (lessThan.lessThanOk n xy_val.1 xy_val.2)
:= by
  unfold ltEq
  have h_1 := FPair.converts_fst h
  have h_2 := FPair.converts_snd h
  clear h
  step lessThan.convertsM_unchecked h_1 h_2 as lt
  step eq.convertsM h_1 h_2 as e
  apply convertsM_pure
  · exact converts_pair h_lt h_e
  · exact fun _ h ↦ h

private lemma step_convertsM [p.AtLeastTwo]
  {state : ClapMState p} {acc le : FArray p 2} {acc_val le_val : Vector Bool 2}
  (h_acc : Converts FArray.conversion state acc acc_val)
  (h_le : Converts FArray.conversion state le le_val)
:
  ConvertsM FArray.conversion (chainStep acc le) state (stepSpec acc_val le_val) True
:= by
  unfold chainStep
  have h_acc0 := FArray.converts_getElem h_acc (show 0 < 2 by omega)
  have h_acc1 := FArray.converts_getElem h_acc (show 1 < 2 by omega)
  have h_le0 := FArray.converts_getElem h_le (show 0 < 2 by omega)
  have h_le1 := FArray.converts_getElem h_le (show 1 < 2 by omega)
  clear h_acc h_le
  step FB.and.convertsM h_acc1 h_le0 as and
  step FB.and.convertsM h_acc1 h_le1 as eqAnd
  step FB.or.convertsM h_acc0 h_and as or
  apply convertsM_pure
  · exact converts_pair h_or h_eqAnd
  · trivial

lemma convertsM_unchecked [p.AtLeastTwo] {n k : ℕ}
  {state : ClapMState p} {a b : FVec p (k + 1)} {a_vals b_vals : Vector (ZMod p) (k + 1)}
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
:
  ConvertsM FB.conversion (bigLessThan n a b) state (raw n a_vals b_vals)
    (∀ i : Fin (k + 1), lessThan.lessThanOk n a_vals[i] b_vals[i])
:= by
  unfold bigLessThan
  have hA := convertsM_mapM_constraints
    (C_elem := FPair.conversion) (C_out := FArray.conversion (k := 2))
    (f_spec := ltEqRaw n)
    (step_constraints := fun xy_val ↦ lessThan.lessThanOk n xy_val.1 xy_val.2)
    (v := a.zip b) (vals := a_vals.zip b_vals)
    (fun i ↦ FVec.converts_zip h_a h_b i.isLt) (fun h ↦ ltEq_convertsM h)
  refine convertsM_of_convertsM (convertsM_bind_and (constraints2 := True) hA ?rest) rfl ?iff
  case iff => simp
  case rest =>
    have h_ltEq := hA.result
    clear h_a h_b
    set ltEqs := (Vector.mapM (ltEq n) (a.zip b)).getResult state.numAlloc state.σ
    set vals := (a_vals.zip b_vals).map (ltEqRaw n)
    have h_elem : ∀ i (h_i : i < k + 1), Converts FArray.conversion
        ((Vector.mapM (ltEq n) (a.zip b)).getState state) ltEqs[i] vals[i] :=
      fun i h_i ↦ converts_getElem_of_vector h_ltEq h_i
    step (convertsM_foldlM (C_acc := FArray.conversion (k := 2)) (C_elem := FArray.conversion (k := 2))
      (f_spec := stepSpec) (v := ltEqs.pop.reverse) (vals := vals.pop.reverse)
      (fun i ↦ by
        simp only [Fin.getElem_fin, Vector.getElem_reverse, Vector.getElem_pop]
        exact h_elem _ (by omega))
      (h_elem k (by omega))
      (fun h_acc h_le ↦ step_convertsM h_acc h_le)) as acc
    apply convertsM_pure
    · exact FArray.converts_getElem h_acc (show 0 < 2 by omega)
    · trivial

/-! ## From the raw chain to `<` on numbers -/

/-- The per-limb bits once both limbs are in range. -/
private def ltEqSpec (xy : ZMod p × ZMod p) : Vector Bool 2 :=
  #v[decide (xy.1.val < xy.2.val), decide (xy.1.val = xy.2.val)]

private lemma stepSpec_init (le : Vector Bool 2) : stepSpec #v[false, true] le = le := by
  ext i h_i
  match i, h_i with
  | 0, _ => simp [stepSpec]
  | 1, _ => simp [stepSpec]

/-- Starting the chain at the top limb is folding every limb from `(false, true)`. -/
private lemma foldl_pop_reverse {k : ℕ} (v : Vector (Vector Bool 2) (k + 1)) :
  v.pop.reverse.foldl stepSpec v[k] = v.toList.foldr (fun le acc ↦ stepSpec acc le) #v[false, true]
:= by
  have h : v.toList = v.pop.toList ++ [v[k]] := by
    rw [Vector.toList_pop, ← List.dropLast_append_getLast (l := v.toList) (by simp),
      List.getLast_eq_getElem]
    simp
  rw [h, List.foldr_append, List.foldr_cons, List.foldr_nil, stepSpec_init,
    ← Vector.foldl_toList, Vector.toList_reverse, List.foldl_reverse]

/-- The chain over in-range limbs, least significant first, decides `<` and `=` of the numbers. -/
private lemma foldr_chain {w : ℕ} :
  ∀ (xs ys : List (ZMod p)), xs.length = ys.length → (∀ x ∈ xs, x.val < 2 ^ w) →
    (∀ y ∈ ys, y.val < 2 ^ w) →
    ((xs.zip ys).map ltEqSpec).foldr (fun le acc ↦ stepSpec acc le) #v[false, true] =
      #v[decide (limbsToNat w xs < limbsToNat w ys), decide (limbsToNat w xs = limbsToNat w ys)]
  | [], [], _, _, _ => by simp
  | a :: xs, b :: ys, h_len, h_xs, h_ys => by
    have ha := h_xs a (by simp)
    have hb := h_ys b (by simp)
    rw [List.zip_cons_cons, List.map_cons, List.foldr_cons,
      foldr_chain xs ys (by simpa using h_len) (fun x hx ↦ h_xs x (by simp [hx]))
        (fun x hx ↦ h_ys x (by simp [hx]))]
    simp only [stepSpec, ltEqSpec, limbsToNat_cons_lt_iff ha hb, limbsToNat_cons_eq_iff ha hb]
    simp

/-- In range, `raw` is `<` on the numbers the limbs encode. -/
lemma raw_eq {n w k : ℕ} {a_vals b_vals : Vector (ZMod p) (k + 1)}
  (h_a : ∀ i : Fin (k + 1), a_vals[i].val < 2 ^ w) (h_b : ∀ i : Fin (k + 1), b_vals[i].val < 2 ^ w)
  (h_wn : w ≤ n) (hn : 2 ^ (n + 1) < p) :
  raw n a_vals b_vals = decide (limbsToNat w a_vals.toList < limbsToNat w b_vals.toList)
:= by
  have : NeZero p := ⟨by have := Nat.one_le_two_pow (n := n + 1); omega⟩
  have h_mem : ∀ {v : Vector (ZMod p) (k + 1)}, (∀ i : Fin (k + 1), v[i].val < 2 ^ w) →
      ∀ x ∈ v.toList, x.val < 2 ^ w := by
    intro v h x hx
    obtain ⟨i, h_i, rfl⟩ := List.getElem_of_mem hx
    simpa using h ⟨i, by simpa using h_i⟩
  have h_n : ∀ {x : ZMod p}, x.val < 2 ^ w → x.val < 2 ^ n :=
    fun h ↦ lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) h_wn)
  have h_spec : (a_vals.zip b_vals).map (ltEqRaw n) = (a_vals.zip b_vals).map ltEqSpec := by
    ext i h_i : 1
    have h₁ : a_vals[i].val < 2 ^ n := h_n (h_a ⟨i, h_i⟩)
    have h₂ : b_vals[i].val < 2 ^ n := h_n (h_b ⟨i, h_i⟩)
    simp only [Vector.getElem_map, Vector.getElem_zip, ltEqRaw, ltEqSpec,
      lessThan.lessThanRaw_eq h₁ h₂ hn, (ZMod.val_injective p).eq_iff]
    rfl
  rw [raw, h_spec, foldl_pop_reverse, Vector.toList_map, Vector.toList_zip,
    foldr_chain _ _ (by simp) (h_mem h_a) (h_mem h_b)]
  rfl

/-- In range, every limb comparison's offset check passes. -/
lemma ok_of {n w k : ℕ} {a_vals b_vals : Vector (ZMod p) (k + 1)}
  (h_a : ∀ i : Fin (k + 1), a_vals[i].val < 2 ^ w) (h_b : ∀ i : Fin (k + 1), b_vals[i].val < 2 ^ w)
  (h_wn : w ≤ n) (hn : 2 ^ (n + 1) < p) :
  ∀ i : Fin (k + 1), lessThan.lessThanOk n a_vals[i] b_vals[i]
:= by
  have h_n : ∀ {x : ZMod p}, x.val < 2 ^ w → x.val < 2 ^ n :=
    fun h ↦ lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) h_wn)
  exact fun i ↦ lessThan.lessThanOk_of (h_n (h_a i)) (h_n (h_b i)) hn

/-- For limbs below `2^w`, `w ≤ n`, the comparison is `<` on the numbers they encode, and it
asserts nothing. -/
lemma convertsM [p.AtLeastTwo] {n w k : ℕ}
  {state : ClapMState p} {a b : FVec p (k + 1)} {a_vals b_vals : Vector (ZMod p) (k + 1)}
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
  (h_a_vals : ∀ i : Fin (k + 1), a_vals[i].val < 2 ^ w)
  (h_b_vals : ∀ i : Fin (k + 1), b_vals[i].val < 2 ^ w)
  (h_wn : w ≤ n) (hn : 2 ^ (n + 1) < p)
:
  ConvertsM FB.conversion (bigLessThan n a b) state
    (decide (limbsToNat w a_vals.toList < limbsToNat w b_vals.toList)) True
:= convertsM_of_convertsM (convertsM_unchecked h_a h_b)
    (raw_eq h_a_vals h_b_vals h_wn hn) (iff_true_intro (ok_of h_a_vals h_b_vals h_wn hn))


end bigLessThan

section examples

private def evalBigLessThan {k : ℕ} (q : ℕ) [q.AtLeastTwo] (n : ℕ) (a b : Vector (ZMod q) (k + 1)) :
    Option (ZMod q) :=
  let cmd : ClapM q (HashConsSt q × FB q) := do
    let a ← a.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let b ← b.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let r ← bigLessThan n a b
    let σ ← getThe (HashConsSt q)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

-- equal
example : evalBigLessThan Primes.babybear 16 #v[5, 7, 9] #v[5, 7, 9] = some 0 := by native_decide
-- the top limb decides
example : evalBigLessThan Primes.babybear 16 #v[9, 7, 3] #v[0, 0, 4] = some 1 := by native_decide
example : evalBigLessThan Primes.babybear 16 #v[0, 0, 5] #v[9, 9, 4] = some 0 := by native_decide
-- equal top limbs, the middle one decides
example : evalBigLessThan Primes.babybear 16 #v[9, 2, 5] #v[0, 3, 5] = some 1 := by native_decide
-- only the low limb differs
example : evalBigLessThan Primes.babybear 16 #v[3, 2, 5] #v[4, 2, 5] = some 1 := by native_decide
example : evalBigLessThan Primes.babybear 16 #v[4, 2, 5] #v[3, 2, 5] = some 0 := by native_decide
-- a single limb
example : evalBigLessThan Primes.babybear 16 #v[3] #v[4] = some 1 := by native_decide
-- Aptos' shape: `BigLessThan(252, ·)` on 64-bit limbs, at bn254
example : evalBigLessThan Primes.bn254 252 #v[2^64 - 1, 1] #v[0, 2] = some 1 := by native_decide
example : evalBigLessThan Primes.bn254 252 #v[0, 2] #v[2^64 - 1, 1] = some 0 := by native_decide

end examples

end Clap.Lang.BigInt
