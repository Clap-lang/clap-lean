import Clap.Primes
import Clap.Spec
import Clap.Lang
import Clap.PoseidonVec.Constant
import Clap.Compiler.Traverse

namespace Clap.PoseidonVec

open Clap Lang

abbrev p := Primes.bn254

variable [Core p] -- not a concrete instance

open Core

/-- **Sigma (S-box):** The sole source of nonlinearity in the Poseidon permutation

    Mirrors circomlib's `Sigma` template -/
def sigma (x : F p) : Option (F p) := do
  let x2 ← some (share (x * x))
  let x4 ← some (share (x2 * x2))
  some (x4 * x)

/-- **Ark (Add Round Constants):** Adds pre-computed round constants to every
    element of the state vector at a given round offset

    Mirrors circomlib's `Ark(t, C, r)` -/
def ark {t c : ℕ} (state : Vector (F p) t) (C : Vector (F p) c) (r : ℕ) : Vector (F p) t :=
  state.mapIdx (fun i s ↦ s + C[i + r]'sorry)

/-- **Mix (MDS matrix multiplication):** Multiplies the state vector by a
    Maximum Distance Separable matrix

    Mirrors circomlib's `Mix(t, M)` template: `out[i] = Σⱼ M[j][i] · in[j]` -/
def mix {t : ℕ} (state : Vector (F p) t) (M : Vector (Vector (F p) t) t) : Vector (F p) t :=
  state.mapIdx (fun (i : ℕ) _ ↦
    (state.zipWith (fun (sj : F p) (row : Vector (F p) t) ↦ row[i]'sorry * sj) M).sum)

-- TODO: Imperative or functional style?
-- def mix (state : Array (F p)) (m : Array (Array (F p))) : Array (F p) := Id.run do
--   let t : ℕ := state.size               -- TODO this will be known at compile time?
--   let mut out : Array (F p) := #[]
--   for i in [:t] do
--     let mut acc : F p := 0
--     for j in [:t] do
--       acc := acc + ((m[j]'sorry)[i]'sorry * state[j]'sorry)
--     out := out.push acc
--   return out

/-- **MixLast:** Produces a single output element by computing column `s` of the
    MDS matrix–vector product. Used in the final round to extract only the
    needed output(s) without computing the full mix

    Mirrors circomlib's `MixLast(t, M, s)` template: `out = Σⱼ M[j][s] · in[j]` -/
def mixLast {t : ℕ} (state : Vector (F p) t) (M : Vector (Vector (F p) t) t) (s : ℕ) : F p :=
  (state.zipWith (fun (sj : F p) (row : Vector (F p) t) ↦ row[s]'sorry * sj) M).sum

-- TODO: Imperative or functional style?
-- def mixLast (s : ℕ) (state : Array (F p)) (m : Array (Array (F p))) : F p := Id.run do
--   let mut acc : F p := 0
--   for j in [:state.size] do
--     acc := acc + (m[j]'sorry)[s]'sorry * state[j]'sorry
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
    (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]'sorry * S[base + t + i]'sorry)

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
--       acc := acc + s[base + i]'sorry * state[i]'sorry
--     return acc
--   /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` — identity + in[0] correction -/
--   sparseCorrection (base t i : ℕ) : F p :=
--     state[i]'sorry + state[0]'sorry * s[base + t + i - 1]'sorry

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
  let nRoundsP : ℕ := N_ROUNDS_P[t - 2]'sorry
  let half : ℕ := nRoundsF / 2

  let state : Vector (F p) t := #v[initState] ++ inputs

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
    let s0 := (← sigma state[0]) + C[(half + 1) * t + r]'sorry
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

def liftVec {n} (xs : Vector (ZMod p) n) : Vector (F p) n := xs.map const
def liftMat {n} (xs : Vector (Vector (ZMod p) n) n) : Vector (Vector (F p) n) n := xs.map (·.map const)

def poseidonBN254 {n} (inputs : Vector (F bn254) n) : Option (F bn254) :=
  let t := 1 + n -- element 2 is at list index 0 and so on
  let C := Clap.PoseidonVec.Constant.C t
  let S := Clap.PoseidonVec.Constant.S t
  let M := Clap.PoseidonVec.Constant.M t
  let P := Clap.PoseidonVec.Constant.P t
  poseidon inputs (liftVec C) (liftVec S) (liftMat M) (liftMat P)

end Poseidon254

end Clap.PoseidonVec

namespace Clap.PoseidonVec.Test

abbrev p := Primes.bn254

open Clap Lang Core
open Clap Lang ZMod
open Clap PoseidonVec

-- circomlib test vector: hash([1, 2]) with t=3
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L50
example : poseidonBN254 #v[1, 2] = some 7853200120776062878684798364095072458815029376092732009249414926327459813530
  := by native_decide

-- circomlib test vector: hash([3, 4]) with t=3
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L60
example : poseidonBN254 #v[3, 4] = some 14763215145315200506921711489642608356394854266165572616578112107564877678998
  := by native_decide

-- circomlib test vector: hash([1, 2, 0, 0, 0]) with t=6
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L29
example : poseidonBN254 #v[1, 2, 0, 0, 0] = some 1018317224307729531995786483840663576608797660851238720571059489595066344487
  := by native_decide

-- circomlib test vector: hash([3, 4, 5, 10, 23]) with t=6
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L39
example : poseidonBN254 #v[3, 4, 5, 10, 23] = some 13034429309846638789535561449942021891039729847501137143363028890275222221409
  := by native_decide

section

open Lean Meta Clap Compiler Simp API CompileSets

-- example {inputs : Vector (F Primes.bn254) 2} : List.foldlM
--   (fun state r => do
--     let l ← Vector.mapM sigma state
--     some (mix (ark l (liftVec (Constant.C (1 + 2))) (3 * r + 3)) (liftMat (Constant.M (1 + 2)))))
--   (ark (#v[0].append inputs) (liftVec (Constant.C (1 + 2))) 0) (List.range (8 / 2 - 1)) = sorry := by
--   simp? +singlePass +arith

/-- Run poseidon on `ZMod bn254` inputs, looking up constants by `t`. -/
private def testPoseidon (inputs : Vector (ZMod p) 2) (expected : F p) : Option Unit := do
  let res ← poseidonBN254 inputs
  F.assert_eq res expected
-- bind (poseidonBN254 inputs) >>= fun res ↦ F.assert_eq res expected
-- process (poseidonBN254 inputs) | push 
def poseidonBN254 : SimpSet :=
  SimpSet.withAllPost #[
    ``PoseidonVec.poseidonBN254, ``poseidon, ``poseidonEx, ``liftVec, ``liftMat,
    ``ark, ``sigma, ``const, ``id,
    ``Constant.C, ``Constant.M, ``Constant.P, ``Constant.S, ``mix,
    ``Constant.C.C02,
    ``Constant.C.C03,
    ``Constant.C.C04,
    ``Constant.C.C05,
    ``Constant.C.C06,
    ``Constant.C.C07,
    ``Constant.C.C08,
    ``Constant.C.C09,
    ``Constant.C.C10,
    ``Constant.C.C11,
    ``Constant.C.C12,
    ``Constant.C.C13,
    ``Constant.C.C14,
    ``Constant.C.C15,
    ``Constant.C.C16,
    ``Constant.C.C17
  ]
#check bind_map_left
#check map_pure
example : [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64,
    68][1 + 2 - 2] = sorry := by
  simp +singlePass

#eval crossEmoji
-- set_option trace.Clap.Compile.simp.fail true
set_option trace.Meta.Tactic.simp true
set_option trace.Clap.Compile true
#check ite_false
set_option maxHeartbeats 200000
#guard_msgs in
#eval show Elab.TermElabM _ from do
  Compiler.compile
    (((←getEnv).find? ``testPoseidon).get!.value!)
    (poseidonBN254 ∪
     CompileSets.Vector.append ∪
     CompileSets.Vector.foldlM ∪
     CompileSets.Vector.mapIdx ∪
     CompileSets.Vector.map ∪
     CompileSets.Vector.mapM ∪
     CompileSets.Nat.arith ∪
     CompileSets.Array.range ∪
     CompileSets.List.range ∪
     CompileSets.Logic.cases ∪ 
     CompileSets.Vector.getElem! ∪
     CompileSets.Vector.sum ∪
     CompileSets.Vector.explode ∪
     CompileSets.Vector.zipWith
     ) true >>= (liftM ∘ PrettyPrinter.ppExpr)

end

end Clap.PoseidonVec.Test
