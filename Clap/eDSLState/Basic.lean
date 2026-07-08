-- import Clap.Circuit

-- import Clap.eDSLState.Wheels

-- namespace Clap

-- namespace Circuit

-- section

-- def p : ℕ := 57

-- variable {var : Type}


-- def pretty [Repr var] [Index var] (c : Circuit p var) := repr 0 c

-- end

-- end Circuit

-- abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ
-- abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

-- def FixedExp.eval {p : ℕ} (varStore : ℕ → Option (ZMod p)) (x : FixedExp p) : Option (ZMod p) :=
--   match x with
--   | .c x => .some x
--   | .v x => varStore x
--   | .add l r => do (←eval varStore l) + (←eval varStore r)
--   | .sub l r => do (←eval varStore l) - (←eval varStore r)
--   | .mul l r => do (←eval varStore l) * (←eval varStore r)

-- inductive CircuitusPlanus (p : ℕ) where
--   | eq0 (e : FixedExp p)
--   | lam
--   | share (e : FixedExp p)
--   | isZero (e : FixedExp p)
--   | num2bits (w : ℕ) (e : FixedExp p)
--   deriving Repr

-- abbrev Circuitus (p : ℕ) := Array (CircuitusPlanus p)

-- namespace Edsl

-- section

-- variable {p : ℕ}

-- structure CircuitState (p : ℕ) where
--   numAlloc : ℕ
--   circuit : Circuitus p
--   deriving Repr

-- def CircuitState.init (p : ℕ) : CircuitState p := ⟨0, #[]⟩

-- abbrev CircuitStateM (p : ℕ) (α : Type) : Type := StateM (CircuitState p) α

-- def CircuitStateM.push {p : ℕ} (op : CircuitusPlanus p) : CircuitStateM p Unit := do
--   let σ ← get
--   set {σ with circuit := σ.circuit.push op}

-- def CircuitStateM.alloc {p : ℕ} : CircuitStateM p ℕ :=
--   (·.1) <$> getModify fun σ ↦ {σ with numAlloc := σ.numAlloc + 1}

-- def CircuitStateM.run (α : Type) (m : CircuitStateM p α) : CircuitState p :=
--   (·.2) <$> StateT.run m (CircuitState.init _)

-- structure CircuitResult (p : ℕ) where
--   numAlloc : ℕ
--   varStore : Std.ExtTreeMap ℕ (ZMod p)
--   constraints : Prop

-- def CircuitResult.step {p : ℕ} (result : CircuitResult p) (next : CircuitusPlanus p) : CircuitResult p :=
--   let ⟨numAlloc, varStore, constraints⟩ := result
--   match next with
--     | .eq0 e => ⟨
--       numAlloc,
--       varStore,
--       constraints ∧ (e.eval varStore.get?) = .some 0
--     ⟩
--     | .lam => ⟨
--       numAlloc + 1,
--       varStore,
--       constraints
--     ⟩
--     | .share e => ⟨
--       numAlloc + 1,
--       varStore.insert numAlloc ((e.eval varStore.get?).getD 0),
--       constraints ∧ (e.eval varStore.get?).isSome
--     ⟩
--     | .isZero e => ⟨
--       numAlloc + 1,
--       varStore.insert numAlloc (if (e.eval varStore.get?) = .some 0 then 1 else 0),
--       constraints ∧ (e.eval varStore.get?).isSome
--     ⟩
--     | .num2bits width e => ⟨
--       numAlloc + width,
--       varStore.insertMany ((Vector.range width).zip (num2bitsLsbPureV width ((e.eval varStore.get?).getD 0))),
--       constraints ∧ (e.eval varStore.get?).isSome
--     ⟩

-- def CircuitState.eval {p : ℕ} (circuit : CircuitState p) (varStore : Std.ExtTreeMap ℕ (ZMod p)) : CircuitResult p :=
--   circuit.circuit.foldl CircuitResult.step ⟨circuit.numAlloc, varStore, True⟩

-- lemma CircuitResult.ext {p : ℕ} {r1 r2 : CircuitResult p}
--   (h_numAlloc : r1.numAlloc = r2.numAlloc)
--   (h_varStore : r1.varStore = r2.varStore)
--   (h_constraints : r1.constraints = r2.constraints)
-- :
--   r1 = r2
-- := by
--   obtain ⟨a1, b1, c1⟩ := r1
--   obtain ⟨a2, b2, c2⟩ := r2
--   simp_all

-- lemma CircuitResult.foldl_step_numAlloc_independent_of_constraints
--   {numAlloc : ℕ}
--   {varStore : Std.ExtTreeMap ℕ (ZMod p)}
--   {constraints1 constraints2 : Prop}
--   {circuit : Circuitus p}
-- :
--   (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints1⟩).numAlloc =
--   (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints2⟩).numAlloc
-- := by
--   obtain ⟨list⟩ := circuit
--   rewrite [←List.reverse_reverse list]
--   induction list.reverse with
--     | nil =>
--       simp
--     | cons head tail h_tail =>
--       simp at h_tail
--       simp
--       set x := List.foldr _ _ _
--       set y := List.foldr _ _ _
--       cases head
--       all_goals simp [CircuitResult.step, h_tail]

-- lemma CircuitResult.foldr_step_numAlloc_independent_of_constraints
--   {numAlloc : ℕ}
--   {varStore : Std.ExtTreeMap ℕ (ZMod p)}
--   {constraints1 constraints2 : Prop}
--   {circuit : List (CircuitusPlanus p)}
-- :
--   (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints1⟩ circuit).numAlloc =
--   (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints2⟩ circuit).numAlloc
-- := by
--   rewrite [←List.reverse_reverse circuit]
--   simp only [List.foldr_reverse, ←List.foldl_toArray]
--   exact CircuitResult.foldl_step_numAlloc_independent_of_constraints

-- lemma CircuitResult.foldl_step_varStore_independent_of_constraints
--   {numAlloc : ℕ}
--   {varStore : Std.ExtTreeMap ℕ (ZMod p)}
--   {constraints1 constraints2 : Prop}
--   {circuit : Circuitus p}
-- :
--   (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints1⟩).varStore =
--   (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints2⟩).varStore
-- := by
--   obtain ⟨list⟩ := circuit
--   rewrite [←List.reverse_reverse list]
--   induction list.reverse with
--     | nil =>
--       simp
--     | cons head tail h_tail =>
--       simp at h_tail
--       simp
--       set x := List.foldr _ _ _
--       set y := List.foldr _ _ _
--       have h_numAlloc : x.numAlloc = y.numAlloc := CircuitResult.foldr_step_numAlloc_independent_of_constraints
--       cases head
--       all_goals simp [CircuitResult.step, h_tail, h_numAlloc]

-- lemma CircuitResult.foldr_step_varStore_independent_of_constraints
--   {numAlloc : ℕ}
--   {varStore : Std.ExtTreeMap ℕ (ZMod p)}
--   {constraints1 constraints2 : Prop}
--   {circuit : List (CircuitusPlanus p)}
-- :
--   (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints1⟩ circuit).varStore =
--   (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints2⟩ circuit).varStore
-- := by
--   rewrite [←List.reverse_reverse circuit]
--   simp only [List.foldr_reverse, ←List.foldl_toArray]
--   exact CircuitResult.foldl_step_varStore_independent_of_constraints

-- lemma CircuitResult.foldl_step_constraints_and
--   {result : CircuitResult p}
--   {circuit : Circuitus p}
-- :
--   (circuit.foldl CircuitResult.step result).constraints = (
--     result.constraints ∧
--     (circuit.foldl CircuitResult.step ⟨result.numAlloc, result.varStore, True⟩).constraints
--   )
-- := by
--   obtain ⟨list⟩ := circuit
--   rewrite [←List.reverse_reverse list]
--   induction list.reverse with
--     | nil =>
--       simp
--     | cons head tail h_tail =>
--       simp at h_tail
--       simp
--       set x := List.foldr _ _ _
--       set y := List.foldr _ _ _
--       have h_varStore : x.varStore = y.varStore := CircuitResult.foldr_step_varStore_independent_of_constraints
--       cases head
--       all_goals simp [CircuitResult.step, h_tail, h_varStore, and_assoc]

-- lemma CircuitState.eval_append
--   {p : ℕ}
--   {numAlloc}
--   {circuit1 circuit2 : Circuitus p}
--   {varStore}
-- :
--   CircuitState.eval ⟨numAlloc, circuit1 ++ circuit2⟩ varStore = (
--     let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := CircuitState.eval ⟨numAlloc, circuit1⟩ varStore
--     let ⟨numAllocPost, varStorePost, constraintsPost⟩ := CircuitState.eval ⟨numAllocMid, circuit2⟩ varStoreMid
--     ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩
--   )
-- := by
--   simp [CircuitState.eval]
--   set first := Array.foldl _ _ circuit1
--   apply CircuitResult.ext
--   all_goals dsimp
--   . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
--   . exact CircuitResult.foldl_step_varStore_independent_of_constraints
--   . exact CircuitResult.foldl_step_constraints_and

-- def well_behaved {α : Type} (action : CircuitStateM p α) : Prop :=
--   ∀ state, ∃ alloced rest, (action state).2 = ⟨state.numAlloc + alloced, state.circuit.append rest⟩

-- lemma CircuitState.eval_bind
--   (α β: Type)
--   (varStore : Std.ExtTreeMap ℕ (ZMod p))
--   (action : CircuitStateM p α)
--   (function : α → CircuitStateM p β)
--   (h_well_behaved : ∀ a, well_behaved (function a))
-- :
--   CircuitState.eval (CircuitStateM.run β (bind action function)) varStore = {
--     numAlloc := sorry
--     varStore := sorry
--     constraints := sorry
--   }
-- := by
--   simp [CircuitStateM.run, bind, init, Functor.map, StateT.run, StateT.bind]
--   obtain ⟨data, state_post_action⟩ := action _
--   dsimp
--   replace h_well_behaved := h_well_behaved data
--   simp [well_behaved] at h_well_behaved
--   obtain ⟨alloced, rest, h⟩ := h_well_behaved state_post_action
--   simp [h]
--   rewrite [CircuitState.eval_append]
--   simp
--   split_ands

-- section

-- variable {var : Type}

-- @[irreducible]
-- def eq0 (e : FixedExp p) : CircuitStateM p Unit := do
--   CircuitStateM.push (.eq0 e)

-- @[irreducible]
-- def lam : CircuitStateM p (FixedExp p) := do
--   CircuitStateM.push (.lam)
--   let varIdx ← CircuitStateM.alloc
--   return .v varIdx

-- @[irreducible]
-- def share (e : FixedExp p) : CircuitStateM p (FixedExp p) := do
--   CircuitStateM.push (.share e)
--   let varIdx ← CircuitStateM.alloc
--   return .v varIdx

-- @[irreducible]
-- def isZero (e : FixedExp p) : CircuitStateM p (FixedExp p) := do
--   CircuitStateM.push (.isZero e)
--   let varIdx ← CircuitStateM.alloc
--   return .v varIdx

-- @[irreducible]
-- def num2bits (width : ℕ) (e : FixedExp p) : CircuitStateM p (Vector (FixedExp p) width) := do
--   CircuitStateM.push (.isZero e)
--   Vector.ofFnM fun _ ↦ do
--     let varIdx ← CircuitStateM.alloc
--     return .v varIdx

-- def testWithInput (x : ZMod 57) : CircuitStateM 57 Unit := do
--   eq0 (.c x)
--   let y ← share (.add 1 1)
--   discard <| [1, 2, y].mapM eq0
--   eq0 4

-- def test : CircuitStateM p Unit := do
--   let x ← lam
--   eq0 x
--   let y ← share (.add 1 1)
--   discard <| [1, 2, y].mapM eq0
--   eq0 4

-- #eval test.run (p := 57)

-- -- Something like this?
-- -- Aaanyway... now I need to make sure to produce `.lam`s from initial arguments

-- end

-- end

-- end Edsl

-- -- @[irreducible]
-- -- def isZero (e : Exp p var) : CircuitContM p var var :=
-- --   Clap.Circuit.isZero e

-- -- @[irreducible]
-- -- def num2bits (w : ℕ) (e : Exp p var) : CircuitContM p var (List var) :=
-- --   Clap.Circuit.num2bits w e

-- -- end

-- -- end

-- -- end Edsl

-- -- namespace Examples

-- -- def TestPrime := 521

-- -- instance : Fact (Nat.Prime TestPrime) := ⟨by native_decide⟩

-- -- instance X : Circuit.Index (ZMod TestPrime) := ⟨fun x ↦ (x : ZMod _)⟩

-- -- open Lang Edsl

-- -- variable {p : ℕ}

-- -- namespace EvalRandom

-- -- def random {var : Type} (a : Exp p var) : CircuitContM p var (FB p) := do
-- --   eq0 (a - 42)
-- --   return 4

-- -- def random' (var : Type) : CircuitContM p var Unit := do
-- --   let x ← random 42
-- --   eq0 x

-- -- def randomOption {var : Type} (a : Exp p var) : Option (FB p) := sorry

-- -- def eval {var} : Circuit p var → denotation var := sorry

-- -- example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
-- --   (h : a = 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = eval ((pure 4 >>= c) fun _ ↦ .nil) := by
-- --   sorry
-- --   done

-- -- lemma CircuitContM.pure_def {var α} {x} :
-- --   (pure x : CircuitContM p var α) = fun f ↦ f x := rfl

-- -- lemma CircuitContM.bind_def {var α} {x} {f : α → CircuitContM p var α} :
-- --   bind (m := CircuitContM p var) x f = fun g => x fun i => f i g := rfl

-- -- open Classical in
-- -- example {var β : Type} {a : Exp p var} {c : FB p → Circuit p var}
-- --   :
-- --   eval (random a c) =
-- --   if a = 42
-- --   then eval ((pure 4 : CircuitContM p var (FB p)) c)
-- --   else .n := by
-- --   rw [CircuitContM.pure_def]
-- --   dsimp
-- --   unfold random
-- --   split_ifs with h
-- --   rw [h]
-- --   simp
-- --   repeat sorry

-- -- example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
-- --   (h : a = 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = eval (c 4 fun _ ↦ .nil) := by
-- --   sorry

-- -- example {var β : Type} {a : Exp p var} {c : FB p → CircuitContM p var β}
-- --   (h : a ≠ 42) : eval ((random a >>= c) (fun _ ↦ .nil)) = .n := by
-- --   sorry

-- -- -- `if a = 42 then eval (c 4 fun _ ↦ .nil) else .n`

-- -- -- #eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random (p := TestPrime) (ZMod TestPrime) 5))
-- -- -- #eval @Clap.Circuit.pretty _ _ _ X (@Clap.Edsl.CircuitContM.run _ _ _ (random' (p := TestPrime) 5 (ZMod TestPrime)))

-- -- end EvalRandom

-- -- -- end
-- -- -- end LessThan

-- -- end Examples

-- end Clap
