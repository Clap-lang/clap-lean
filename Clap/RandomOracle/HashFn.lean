import Clap.Util.Primes

/-!
# Hash families, and the queries a random oracle answers

`HashFn` is what the library knows of a hash: some function of its inputs, at every arity. The
Poseidon circuit computes one (`Lang.Poseidon.Computes`), and a random function on `Query`s reads as
one (`Query.toHashFn`). This file is pure: no circuits and no probability.
-/

namespace Clap.RandomOracle

open Primes

/-- A hash family. circomlib's `Poseidon(n)` uses different round
constants at each width, so this is a family of functions -/
abbrev HashFn := ∀ {n : ℕ}, Vector (ZMod bn254) n → ZMod bn254

/-- One call to Poseidon is denoted as query. A query is a pair `⟨n, v⟩`:
* `n` is how many inputs are hashed (the *arity*);
* `v : Fin n → ZMod bn254` is the list of those `n` inputs, `v 0` up to `v (n - 1)`.

For example, hashing the three field elements `a, b, c` is the query `⟨3, ![a, b, c]⟩`.

The random oracle gives back one field element for each query. Since `n` is part of the query,
hashing 3 inputs and hashing 4 inputs are unrelated.

`n` ranges over `Fin 17`. `16` is the largest number of inputs circomlib's Poseidon accepts, and so the largest `Computes`
covers. -/
abbrev Query := Σ n : Fin 17, (Fin n → ZMod bn254)

/-- Read a function on queries as a hash family -/
def Query.toHashFn (f : Query → ZMod bn254) : HashFn :=
  fun {n} v ↦ if h : n < 17 then f ⟨⟨n, h⟩, fun i ↦ v[i]⟩ else 0

/-- Coordinate `j` of a query, `0` past its arity. -/
def Query.coord (q : Query) (j : ℕ) : ZMod bn254 :=
  if h : j < q.1.val then q.2 ⟨j, h⟩ else 0

/-- The query `Query.toHashFn f` asks when it hashes `u` (arity `k ≤ 16`). -/
def hashQ {k : ℕ} (u : Vector (ZMod bn254) k) : Query :=
  if h : k < 17 then ⟨⟨k, h⟩, fun i ↦ u[i]⟩ else ⟨0, Fin.elim0⟩

lemma toHashFn_apply (f : Query → ZMod bn254) {k : ℕ} (u : Vector (ZMod bn254) k) (h : k < 17) :
    Query.toHashFn f u = f (hashQ u) := by
  simp [Query.toHashFn, hashQ, h]

lemma coord_hashQ {k : ℕ} (u : Vector (ZMod bn254) k) (h : k < 17) (j : ℕ) :
    (hashQ u).coord j = if hj : j < k then u[j] else 0 := by
  rw [hashQ, dif_pos h]
  simp [Query.coord]

end Clap.RandomOracle
