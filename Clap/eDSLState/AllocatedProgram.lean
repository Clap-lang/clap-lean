import Clap.eDSLState.Monad
import Clap.eDSLState.Convert.Specialised
import Clap.eDSLState.ConstraintSystem.toCs
import Clap.eDSLState.PublicInput
import Clap.eDSLState.Wheels
import Clap.eDSLState.WitnessGenerator.toWg
import Clap.Poseidon.NewPoseidon
import Clap.Lang.FUnit.assert_eq

namespace Clap

open Lang

/--
Recall that `HashConsM` lifts to `ClapM`.

`AllocatedProgram` allows us to treat inputs received in a Lean function as 'circuit public inputs',
appropriately allocated in the underlying `ClapM` state.

The action `allocate` is the allocator of `numAlloc` allocations for the given `program`.
Note that `liftM allocate >>= program` is a valid composition in `ClapM`.

NB:
Technically, `allocate` should actually just fill the `numAlloc`, but whatever.
This will likely just be used once at the top level (depending on the proof structure),
and we have the ingredients for keyless. Namely: in `Clap/Keyless/Allocate.lean` we have:
- allocateKeyless : `HashConsM p (FKeylessInput p)`, i.e. the `allocate` function
- allocateKeylessWidth : `ℕ`, i.e. the `numAlloc`
-/
structure AllocatedProgram (p : ℕ) where
  InputT : Type
  program : InputT → ClapM p Unit
  numAlloc : ℕ
  allocate : HashConsM p InputT

namespace AllocatedProgram

/-
One can treat these opaquely really.
-/

/--
Recall that `ClapM.getCircuit` and `ClapM.getHashConsState` both `run` the `ClapM`,
starting allocations at some `numAlloc`.

1. `getCircuit` starts with an empty `HashConsSt` and fills it in with necessary expressions
  introduced by the `allocate` function
2. We then build the circuit for the `program`, _notably_ starting at _not_ 0, but at `prog.numAlloc`,
   i.e. we are accounting for the number of allocations introduced by the allocator.
3. We also return the 'bootstrapped' `HashConsState`.
-/
def getCircuit {p} (prog : AllocatedProgram p) : Circuit × HashConsSt p :=
  let (inputs, σ) := prog.allocate.run (HashConsSt.empty p)
  (
    (prog.program inputs).getCircuit prog.numAlloc σ,
    (prog.program inputs).getHashConsState prog.numAlloc σ
  )

/--
Recall that `[Γ, σ, numAlloc|circuit]ₑ` evluates the `circuit` in the `ClapMState`
`⟨Γ, σ, numAlloc⟩`, i.e. varstore, hash-cons state and number of allocations respectively.

- The only trick here is that the varstore `Γ` is constructed by taking the first `prog.numAlloc`
  allocations. NB this is already `HashConsState`-consistent because `σ` is the post-`allocate` `σ`.
-/
def getConstraints {p} (prog : AllocatedProgram p) (inputs : Vector (ZMod p) prog.numAlloc) :=
  let (circuit, σ) := prog.getCircuit
  [.ofArray (inputs.toArray.zipIdx.map Prod.swap), σ, prog.numAlloc|circuit]ₑ.constraints

end AllocatedProgram

section PoseidonExample

/--
Here we say that we have a poseidon program that allocates 2 inputs, first of which compound.
Note that given how the infrastructure works, the `program` here will start 'working'
only after `mkInputVectorF` and `mkInputF` are run, producing an appropriate `ClapMState`.
-/
def poseidonProgram (k : ℕ) : AllocatedProgram Primes.bn254 where
  InputT := Vector (F Primes.bn254) k × F Primes.bn254
  program := fun (input, hash) ↦ do
    let result ← poseidonBN254 input
    assert_eq result hash
  numAlloc := k + 1
  allocate := do
    let (vec, numAlloc) ← mkInputVectorF 0 k
    let (f, _numAlloc) ← mkInputF numAlloc
    return (vec, f)

section Spec

/-
Suppose `poseidonSpec` is a lean function implementing poseidon.
Yes, we have this in our crypto repo, but ::effort::.
-/

opaque poseidonSpec {k} (inputs : Vector (ZMod Primes.bn254) k) : ZMod Primes.bn254

/--
The only sorry in the example.

This says that the circuit `poseidonBN254` conforms to `poseidonSpec`.
Of course, this can't be proven for the `opaque` spec.
-/
theorem poseidon.convertsM
  {k}
  {inputs : Vector (F Primes.bn254) k} {state}
  {input_vals : Vector (ZMod Primes.bn254) k}
  (h : ∀ i : Fin k, Converts F.conversion state inputs[i] input_vals[i])
  :
  ConvertsM F.conversion (poseidonBN254 inputs) state (poseidonSpec input_vals) True := by
  sorry

/--
The spec for the full `program`, i.e. in `ClapM Unit` with the extra `assert_eq`.
-/
theorem PoseidonCircuitSpec
  {k}
  {state}
  {input : Vector (F Primes.bn254) k × F Primes.bn254}
  {input_vals : Vector (ZMod Primes.bn254) k}
  {input_val2 : ZMod Primes.bn254}
  (h₀ : Converts F.conversion state input.2 input_val2)
  (h : ∀ i : Fin k, Converts F.conversion state input.1[i] input_vals[i])
  :
  ConvertsM FUnit.conversion
    ((poseidonProgram k).program input) state ()
    (poseidonSpec input_vals = input_val2) := by
  unfold poseidonProgram
  dsimp
  step poseidon.convertsM h as poseidon
  apply convertsM_of_convertsM (assert_eq.convertsM h_poseidon h₀) rfl
  simp

end Spec

section PoseidonAllocationLemmas

@[simp, grind =]
lemma poseidon_the_envisaged_getResult_length
  {k}
  {σ}
:
  ((poseidonProgram k).allocate.getResult σ).1.toList.length = k
:= by
  simp [poseidonProgram]

@[grind =]
lemma deref_poseidon_allocate_1
  {k}
  {σ}
  {i}
  (h: i < k)
:
  *ₑ⦃
    ((poseidonProgram k).allocate.getResult σ).1[i],
    (poseidonProgram k).allocate.getHashConsState σ
  ⦄ = .some (.v i)
:= by
  simp [
    poseidonProgram,
    mkInputVectorF,
    HashConsM.getHashConsState_bind
  ]
  induction' k with k ih generalising σ
  . grind
  . simp only [Vector.range_succ]
    simp only [Vector.mapM_append]
    by_cases h_i : i = k
    . simp [
        h_i,
        HashConsM.getHashConsState_bind,
        HashConsM.getHashConsState_map
      ]
      rewrite [
        ←varSet.deref_eq_of_ref_eq_prefix
          (e₁ := ⦃((mkInputF k).getResult ((Vector.mapM mkInputF (Vector.range k)).getHashConsState σ)).1, _⦄)
      ]
      case pos.h₂ =>
        simp
        exact isPrefixOf_mkInputF
      . grind
      . rfl
      . grind
    . simp [Vector.getElem_push]
      rewrite [dite_cond_eq_true (by grind)]
      simp [
        HashConsM.getHashConsState_bind,
        HashConsM.getHashConsState_map
      ]
      rewrite [←varSet.deref_eq_of_ref_eq_prefix]
      . exact ih (by grind)
      . simp
      . grind
      . grind

@[simp, grind =]
lemma deref_poseidon_allocate_2
  {k}
  {σ}
:
  *ₑ⦃
    ((poseidonProgram k).allocate.getResult σ).2,
    (poseidonProgram k).allocate.getHashConsState σ
  ⦄ = .some (.v k)
:= by
  simp [
    poseidonProgram,
    mkInputVectorF,
    HashConsM.getHashConsState_bind
  ]

-- TODO name, mov

end PoseidonAllocationLemmas

/--
Important proof.

Note that this relates the underlying state allocations with the 'Lean function input'.
-/
theorem poseidon.converts_input_vec
  {k : ℕ} {input : Vector (ZMod Primes.bn254) (k + 1)}
:
  Converts
  FVec.conversion
  ⟨
    Std.ExtTreeMap.ofArray (Array.map Prod.swap input.toArray.zipIdx) compare,
    ((poseidonProgram k).allocate.getHashConsState (HashConsSt.empty Primes.bn254)),
    k+1
  ⟩
  ((poseidonProgram k).allocate.getResult (HashConsSt.empty Primes.bn254)).1
  ((input.take k).cast (by grind))
:= by
  constructor
  case h_conversion =>
    grind
  case varSet_wf =>
    intro ⟨i, h_i⟩
    simp at ⊢ h_i
    unfold Expr.varSet_wellFormed
    unfold Expr.varSet
    grind
  case expr_wf =>
    intro ⟨i, h_i⟩
    simp at ⊢ h_i
    grind
  case value_eq =>
    intro ⟨i, h_i⟩
    simp at ⊢ h_i
    rewrite [eval_eq_evalRec]
    . unfold Expr.evalRec
      obtain ⟨⟨input⟩, h_input⟩ := input
      simp [
        Std.ExtTreeMap.toArray_eq_toArray,
        Std.ExtTreeMap.ofList_eq_insertMany_empty,
        Std.ExtTreeMap.getElem?_insertMany_eq_getElem?
      ]
      grind
    . grind

-- the requested end-to-end spec
theorem odysseus
  {k}
  {input : Vector (ZMod Primes.bn254) (k + 1)} :
  (poseidonProgram k).getConstraints input ↔
  letI inputInit := input.take k
  letI inputLast := input.back!
  poseidonSpec inputInit = inputLast
:= by
  unfold AllocatedProgram.getConstraints
  dsimp [AllocatedProgram.getCircuit]
  set numAlloc := (poseidonProgram k).numAlloc with eq₁
  simp_rw [←eq₁]
  set varStore := Std.ExtTreeMap.ofArray (Array.map Prod.swap input.toArray.zipIdx) compare with eq₂
  set σ := ((poseidonProgram k).allocate.run (HashConsSt.empty Primes.bn254)).2 with eq₃
  set cmd := (poseidonProgram k).program
               ((poseidonProgram k).allocate.run (HashConsSt.empty Primes.bn254)).1 with eq₄
  set inputRef := ((poseidonProgram k).allocate.run (HashConsSt.empty Primes.bn254)).1 with eq₅
  set state : ClapMState Primes.bn254 := ⟨varStore, σ, numAlloc⟩
  change (cmd.runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔ poseidonSpec (input.extract 0 k) = input.back!
  subst cmd
  rw [(PoseidonCircuitSpec _ _).constraints]
  swap
  exact Vector.cast (by grind) (input.take k)
  swap
  exact input.back!
  simp
  · constructor
    all_goals {
      intros h
      rw [←h]
      congr
      grind
      symm
      rcases input with ⟨array, h⟩
      simp
      grind
    }
  · unfold poseidonProgram
    dsimp
    constructor <;> simp
    · subst σ
      subst state numAlloc
      simp [←HashConsM.getHashConsState.eq_def]
      simp [←HashConsM.getResult.eq_def]
      dsimp [poseidonProgram]
      unfold mkInputF
      simp [Expr.varSet_wellFormed]
      rw [HashConsM.getHashConsState_bind]
      simp
    · subst σ
      subst state numAlloc
      simp [←HashConsM.getHashConsState.eq_def]
      simp [←HashConsM.getResult.eq_def]
      dsimp [poseidonProgram]
      simp [Expr.wellFormed]
      unfold mkInputF
      rw [HashConsM.getHashConsState_bind]
      simp
      exact HashConsM.getResult_lt_getHashConsState_size_mkVar
    · subst σ
      subst state numAlloc
      subst varStore
      simp [←HashConsM.getHashConsState.eq_def]
      simp [←HashConsM.getResult.eq_def]
      dsimp [poseidonProgram]
      unfold mkInputF
      rw [HashConsM.getHashConsState_bind]
      simp
      rw [eval_eq_evalRec (by grind)]
      rw [HashConsM.getResult_mkVar]
      rw [HashConsM.getHashConsState_mkVar]
      unfold Expr.evalRec

      simp_all only [Option.map_eq_map, inputRef]
      split
      next heq =>
        simp_all only [reduceCtorEq]
        (grind)
      next expr heq =>
        split
        next expr h k_1 h_1 =>
          simp_all only [Option.some.injEq]
          subst h
          (grind)
        next expr h idx h_1 =>
          simp_all only [Option.some.injEq]
          subst h
          split at heq
          all_goals {
            rcases input with ⟨⟨a⟩, c⟩
            simp
            have : idx = k := by grind
            subst this
            rw [Std.ExtTreeMap.toArray_eq_toArray]
            rw [Std.ExtTreeMap.ofList_eq_insertMany_empty]
            let aSplit := a.take idx ++ [a.getLast!]
            have : a = aSplit := by
              simp [aSplit]
              ext1 i
              grind
            rw [this]
            simp [aSplit]
            rw [List.zipIdx_append]
            simp
            rw [Std.ExtTreeMap.insertMany_append]
            simp
            grind
          }
        next expr h lhs rhs op h_1 =>
          simp_all only [Option.some.injEq]
          subst h
          (grind)
  · intro ⟨i, h_i⟩
    apply FVec.converts_getElem _ h_i
    exact poseidon.converts_input_vec

end PoseidonExample

end Clap
