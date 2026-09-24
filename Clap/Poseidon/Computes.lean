import Clap.Poseidon.Poseidon
import Clap.Model.Convert.Specialised
import Clap.Lang.Core.Combinators.ofFnM
import Clap.Lang.Core.F.mkF

/-!
A hash function has no functional specification a circuit lemma could be proved against. All
there is to say is that it is some function of its inputs.
-/

namespace Clap.Poseidon

open Lang

/-- A hash family. circomlib's `Poseidon(n)` uses different round
constants at each width, so this is a family of functions -/
abbrev HashFn := ∀ {n : ℕ}, Vector (ZMod Primes.bn254) n → ZMod Primes.bn254

/--
poseidonBN254 ──Computes──▶  H : HashFn  ◀──Query.toHashFn── f ← randomOracle
   (circuit)                (ideal specs                      (random function)
                          are written in H)

 The circuit `poseidonBN254` computes `H`, at every arity it supports (1 to 16 inputs). -/
def Computes (H : HashFn) : Prop :=
  ∀ {n : ℕ} {state : ClapMState Primes.bn254} {xs : FVec Primes.bn254 n}
    {vals : Vector (ZMod Primes.bn254) n},
    0 < n → n ≤ 16 →
    Converts FVec.conversion state xs vals →
    ConvertsM F.conversion (poseidonBN254 xs) state (H vals) True

section evalConst

-- See `HashToField/hashElemsToField.lean`.
attribute [local irreducible] Clap.poseidonBN254

/-- `poseidonBN254` of constant inputs. -/
def constCmd {n : ℕ} (xs : Vector (ZMod Primes.bn254) n) : ClapM Primes.bn254 (F Primes.bn254) :=
  do poseidonBN254 (← Vector.ofFnM fun i ↦ mkF xs[i])

/-- The value `poseidonBN254` computes on constant inputs, read the way `Converts` reads a
result: in the state its own circuit leaves. Computable, so `native_decide` can pin it. -/
def evalConst {n : ℕ} (xs : Vector (ZMod Primes.bn254) n) : Option (ZMod Primes.bn254) :=
  let state := (constCmd xs).getState ⟨{}, {}, 0⟩
  [state.varStore|⦃(constCmd xs).getResult 0 {}, state.σ⦄]

/-- `value_eq` of a field-valued `ConvertsM`, over an arbitrary action. Going through it keeps
the kernel from unfolding the action to match `[r][0]` against `r` (a deterministic timeout). -/
private lemma value_eq_of_convertsM {p : ℕ} {a : ClapM p (F p)} {state : ClapMState p}
    {v : ZMod p} {c : Prop} (h : ConvertsM F.conversion a state v c) :
    [(a.getState state).varStore|⦃a.getResult state.numAlloc state.σ, (a.getState state).σ⦄] =
      some v :=
  h.result.value_eq ⟨0, Nat.one_pos⟩

/-- `Computes` determines `H`: it is what the circuit evaluates to. So every value of `evalConst`
that `native_decide` pins is a value of every `H` with `Computes H`, and the circomlib vectors in
`Poseidon.lean` constrain `H` itself, not only the circuit. -/
lemma Computes.evalConst_eq
  {H : HashFn}
  (h_H : Computes H)
  {n : ℕ}
  (xs : Vector (ZMod Primes.bn254) n)
  (h_pos : 0 < n)
  (h_n : n ≤ 16)
:
  evalConst xs = some (H xs)
:= by
  have h : ConvertsM F.conversion (constCmd xs) ⟨{}, {}, 0⟩ (H xs) True := by
    unfold constCmd
    step convertsM_ofFnM (vals := xs) (fun _ _ ↦ mkF.convertsM) as refs
    apply convertsM_of_convertsM (h_H h_pos h_n h_refs)
    . rfl
    . trivial
  exact value_eq_of_convertsM h

/-- circomlib's `hash([1, 2])` (`test/poseidoncircuit.js#L50`), as a value of `H`. -/
example {H : HashFn} (h_H : Computes H) :
    H #v[1, 2] = 7853200120776062878684798364095072458815029376092732009249414926327459813530 := by
  have h := h_H.evalConst_eq #v[1, 2] (by decide) (by decide)
  rw [show evalConst #v[1, 2] = some
    7853200120776062878684798364095072458815029376092732009249414926327459813530 by
      native_decide] at h
  exact (Option.some.inj h).symm

end evalConst

end Clap.Poseidon
