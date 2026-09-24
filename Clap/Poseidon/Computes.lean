import Clap.Poseidon.Poseidon
import Clap.Model.Convert.Specialised

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

end Clap.Poseidon
