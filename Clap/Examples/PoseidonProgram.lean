import Clap.Model.AllocatedProgram
import Clap.Model.Convert.Specialised
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.PublicInput
import Clap.Model.WitnessGenerator.toWg
import Clap.Util.Containers
import Clap.Poseidon.Poseidon
import Clap.Lang.Core.FUnit.assert_eq
/-!
# A worked `AllocatedProgram`

An end-to-end example: a program that takes `k` field elements plus a claimed hash, computes
Poseidon over the `k` inputs and asserts the result equals the claim. It allocates those
`k + 1` values as public inputs, lowers the whole thing to a constraint system, and proves
that the constraint system holds exactly when the claim is the Poseidon hash of the inputs
(`odysseus`).

This is a demonstration of the public-input layer, not a library. It carries the repo's one
deliberate `sorry`: `poseidon.convertsM` stands in for a `ConvertsM` lemma about
`poseidonBN254`, which has not been proved — the spec it is stated against is the `opaque`
`poseidonSpec` below, so it is unprovable by construction. Everything downstream of it is a
real proof.

See [docs/public-inputs.md](../../docs/public-inputs.md).
-/

namespace Clap

open Lang


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


end Clap
