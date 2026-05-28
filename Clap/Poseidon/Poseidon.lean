import Clap.Primes
import Clap.Spec
import Clap.Lang
import Clap.Poseidon.Constant

namespace Clap.Poseidon

open Clap Lang

abbrev p := Primes.bn254

/-- **Sigma (S-box):** The sole source of nonlinearity in the Poseidon permutation

    Mirrors circomlib's `Sigma` template -/
def sigma (x : F p) : Option (F p) := do
  let x2 ← share (x * x)
  let x4 ← share (x2 * x2)
  some (x4 * x)

/-- **Ark (Add Round Constants):** Adds pre-computed round constants to every
    element of the state vector at a given round offset

    Mirrors circomlib's `Ark(t, C, r)` -/
def ark {t c : ℕ} (state : Vector (F p) t) (C : Vector (F p) c) (r : ℕ) : Vector (F p) t :=
  state.mapIdx (fun i s ↦ s + C[i + r]!)

/-- **Mix (MDS matrix multiplication):** Multiplies the state vector by a
    Maximum Distance Separable matrix

    Mirrors circomlib's `Mix(t, M)` template: `out[i] = Σⱼ M[j][i] · in[j]` -/
def mix {t : ℕ} (state : Vector (F p) t) (M : Vector (Vector (F p) t) t) : Vector (F p) t :=
  state.mapIdx (fun (i : ℕ) _ ↦
    (state.zipWith (fun (sj : F p) (row : Vector (F p) t) ↦ row[i]! * sj) M).sum)

-- TODO: Imperative or functional style?
-- def mix (state : Array (F p)) (m : Array (Array (F p))) : Array (F p) := Id.run do
--   let t : ℕ := state.size               -- TODO this will be known at compile time?
--   let mut out : Array (F p) := #[]
--   for i in [:t] do
--     let mut acc : F p := 0
--     for j in [:t] do
--       acc := acc + ((m[j]!)[i]! * state[j]!)
--     out := out.push acc
--   return out

/-- **MixLast:** Produces a single output element by computing column `s` of the
    MDS matrix–vector product. Used in the final round to extract only the
    needed output(s) without computing the full mix

    Mirrors circomlib's `MixLast(t, M, s)` template: `out = Σⱼ M[j][s] · in[j]` -/
def mixLast {t : ℕ} (state : Vector (F p) t) (M : Vector (Vector (F p) t) t) (s : ℕ) : F p :=
  (state.zipWith (fun (sj : F p) (row : Vector (F p) t) ↦ row[s]! * sj) M).sum

-- TODO: Imperative or functional style?
-- def mixLast (s : ℕ) (state : Array (F p)) (m : Array (Array (F p))) : F p := Id.run do
--   let mut acc : F p := 0
--   for j in [:state.size] do
--     acc := acc + (m[j]!)[s]! * state[j]!
--   return acc

/-- **MixS (Sparse Mix):** Applies the sparse-matrix multiplication used during
    partial rounds

    Mirrors circomlib's `MixS(t, S, r)` template -/
def mixS {t s : ℕ} (r : ℕ) (state : Vector (F p) t) (S : Vector (F p) s) : Vector (F p) t :=
--  let t : ℕ := state.length
  let base : ℕ := (2 * t - 1) * r
  ⟨#[dotProduct base] ++ (tail base).toArray, sorry⟩
where
  /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
  dotProduct (base : ℕ) : F p :=
    let s' : Vector _ t := ⟨S.extract base (base+t) |>.toArray, sorry⟩
    (state.zipWith (· * ·) s').sum
  /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` for `i ∈ [1, t)` -/
  tail (base : ℕ) : Vector (F p) (t-1) :=
    (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]! * S[base + t + i]!)

-- TODO: Imperative or functional style?
-- def mixS (r : ℕ) (state : Array (F p)) (s : Array (F p)) : Array (F p) := Id.run do
--   let t := state.size
--   let base := (2 * t - 1) * r
--   let mut out : Array (F p) := #[dotProduct base t]
--   for i in [1:t] do
--     out := out.push (sparseCorrection base t i)
--   return out
-- where
--   /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
--   dotProduct (base t : ℕ) : F p := Id.run do
--     let mut acc : F p := 0
--     for i in [:t] do
--       acc := acc + s[base + i]! * state[i]!
--     return acc
--   /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` — identity + in[0] correction -/
--   sparseCorrection (base t i : ℕ) : F p :=
--     state[i]! + state[0]! * s[base + t + i - 1]!

/-- **PoseidonEx:** Full Poseidon permutation

    The permutation proceeds in three phases:
    1. **First-half full rounds** (`R_f/2`): `Ark → Sigma_all → Ark → Mix(M)`
    2. **Partial rounds** (`R_p`): Only `state[0]` passes through the S-box,
       then a round constant is added to `state[0]`, and the sparse matrix `S`
       is applied via `MixS`.
    3. **Second-half full rounds** (`R_f/2`): Same structure as phase 1 with
       matrix `M`. The very last round omits Ark and uses `MixLast` to extract
       only the requested `nOuts` output elements.

    Mirrors circomlib's `PoseidonEx(nInputs, nOuts)` template.

    Parameters:
    - `nOuts`     — number of output field elements to produce
    - `inputs`    — input field elements (length = `nInputs`)
    - `initState` — initial capacity element (typically 0)
    - `C`         — flat list of all round constants
    - `S`         — flat list of sparse-matrix entries for partial rounds
    - `M`         — MDS matrix (used in full rounds)
    - `P`         — pre-sparse matrix (used at the boundary of full → partial) -/
def poseidonEx {n c s : ℕ} (inputs : Vector (F p) n) (initState : F p)
    (C : Vector (F p) c) (S : Vector (F p) s) (M P : Vector (Vector (F p) (1+n)) (1+n)) : Option (F p) := do
  -- Poseidon parameters (from circomlib's PoseidonEx template)
  -- N_ROUNDS_P[t-2] for t ∈ [2, 17]
  let N_ROUNDS_P : List ℕ := [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
  let t : ℕ := 1 + n
  let nRoundsF : ℕ := 8
  let nRoundsP : ℕ := N_ROUNDS_P[t - 2]!
  let half : ℕ := nRoundsF / 2

  let state : Vector (F p) t := Vector.append #v[initState] inputs

  -- initial state: [initState, inputs[0], …, inputs[nInputs−1]]
  let state := ark state C 0

  -- Phase 1: first-half full rounds (r = 0 … half−2), mix with M
  let state ← (List.range (half - 1)).foldlM (fun state r ↦ do
    let l ← state.mapM sigma
    mix (ark l C ((r + 1) * t)) M) state

  -- Boundary round (r = half−1): sigma → ark → mix with P
  let state := mix (ark (← state.mapM sigma) C (half * t)) P

  -- Phase 2: partial rounds
  let state ← (List.range nRoundsP).foldlM (fun state r ↦ do
    let s0 := (← sigma state[0]!) + C[(half + 1) * t + r]!
    mixS r (state.set 0 s0) S) state

  -- Phase 3: second-half full rounds (r = 0 … half−2), mix with M
  let state ← (List.range (half - 1)).foldlM (fun state r ↦ do
    let l ← state.mapM sigma
    mix (ark l C ((half + 1) * t + nRoundsP + r * t)) M) state

  -- Final round: sigma on all, then extract nOuts elements via MixLast
  let state ← state.mapM sigma
  mixLast state M 0

/-- **Poseidon:** Single-output Poseidon hash. Wraps `poseidonEx` with
    `nOuts = 1` and `initialState = 0`, returning the first element of
    the permutation output.

    Mirrors circomlib's `Poseidon(nInputs)` template. -/
def poseidon {n c s} (inputs : Vector (F p) n) (C : Vector (F p) c) (S : Vector (F p) s) (M P : Vector (Vector (F p) (1+n)) (1+n)) : Option (F p) := do
  poseidonEx inputs 0 C S M P

section Poseidon254

open Primes

def poseidonBN254 {n} (inputs : Vector (F bn254) n) : Option (F bn254) :=
  let t := 1 + n -- element 2 is at list index 0 and so on
  let C := Clap.Poseidon.Constant.C t
  let S := Clap.Poseidon.Constant.S t
  let M := Clap.Poseidon.Constant.M t
  let P := Clap.Poseidon.Constant.P t
  poseidon inputs C S M P

end Poseidon254

end Clap.Poseidon

namespace Clap.Poseidon.Test

abbrev p := Primes.bn254

open Clap Lang Poseidon

-- circomlib test vector: hash([1, 2]) with t=3
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L50
example : poseidonBN254 #v[1, 2] = some
  7853200120776062878684798364095072458815029376092732009249414926327459813530
  := by native_decide

-- circomlib test vector: hash([3, 4]) with t=3
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L60
example : poseidonBN254 #v[3, 4] = some
  14763215145315200506921711489642608356394854266165572616578112107564877678998
  := by native_decide

-- circomlib test vector: hash([1, 2, 0, 0, 0]) with t=6
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L29
example : poseidonBN254 #v[1, 2, 0, 0, 0] = some
  1018317224307729531995786483840663576608797660851238720571059489595066344487
  := by native_decide

-- circomlib test vector: hash([3, 4, 5, 10, 23]) with t=6
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L39
example : poseidonBN254 #v[3, 4, 5, 10, 23] = some
  13034429309846638789535561449942021891039729847501137143363028890275222221409
  := by native_decide

-- The vectors below come from arnaucube's `poseidon-ark` reference suite (https://github.com/arnaucube/poseidon-ark/blob/master/src/lib.rs#L160-L240),
-- which is the canonical bn254 Poseidon implementation Aptos's `aptos_crypto::poseidon_bn254` is benchmarked against (see the comment at https://github.com/aptos-labs/aptos-core/blob/main/crates/aptos-crypto/src/poseidon_bn254/mod.rs#L128).
-- They cover arities used by the Keyless circuit but missing from the four circomlib `poseidoncircuit.js` tests above:
-- - arity 4  → `computeIdentityCommitment` (Poseidon over 4 inputs)
-- - arity 6  → `verifyNonce` (Poseidon over 6 inputs)
-- - arity 14 → `verifyPublicInputsHash` (Poseidon over 14 inputs)

-- arity 1: hash([1])
example : poseidonBN254 #v[1] = some
  18586133768512220936620570745912940619677854269274689475585506675881198879027
  := by native_decide

-- arity 4: hash([1, 2, 3, 4] = some) — also matches circomlibjs's `poseidonperm_x5_254_5`
-- (https://github.com/iden3/circomlibjs/blob/main/test/poseidon.js)
example : poseidonBN254 #v[1, 2, 3, 4] = some
  18821383157269793795438455681495246036402687001665670618754263018637548127333
  := by native_decide

-- arity 6: hash(#v[1, 2, 0, 0, 0, 0] = some)
example : poseidonBN254 #v[1, 2, 0, 0, 0, 0] = some
  15336558801450556532856248569924170992202208561737609669134139141992924267169
  := by native_decide

-- arity 6: hash(#v[1, 2, 3, 4, 5, 6] = some)
example : poseidonBN254 #v[1, 2, 3, 4, 5, 6] = some
  20400040500897583745843009878988256314335038853985262692600694741116813247201
  := by native_decide

-- arity 14: hash(#v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = some)
example : poseidonBN254 #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = some
  8354478399926161176778659061636406690034081872658507739535256090879947077494
  := by native_decide

-- arity 14: hash(#v[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0] = some)
example : poseidonBN254 #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0] = some
  5540388656744764564518487011617040650780060800286365721923524861648744699539
  := by native_decide

-- arity 16: hash(#v[1, …, 16] = some)
example : poseidonBN254 #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] = some
  9989051620750914585850546081941653841776809718687451684622678807385399211877
  := by native_decide

-- arity 16: hash(#v[1, …, 9, 0×7] = some)
example : poseidonBN254 #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0] = some
  11882816200654282475720830292386643970958445617880627439994635298904836126497
  := by native_decide

end Poseidon.Test
