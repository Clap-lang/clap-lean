import Clap.Primes
import Clap.Spec
import Clap.Lang
import Clap.Poseidon.Constant
--import Clap.Compiler.Wheels
import Clap.Compiler.Reduce
import Clap.Test.Compilation.Dummy
--import Clap.Compiler.Cimplol

namespace Clap.Poseidon

open Clap Lang

abbrev p := Primes.bn254

variable [Core p] -- not a concrete instance

open Core

/-- **Sigma (S-box):** The sole source of nonlinearity in the Poseidon permutation

    Mirrors circomlib's `Sigma` template -/
def sigma (x : F p) : Option (F p) := do
  let x2 ← share (x * x)
  let x4 ← share (x2 * x2)
  x4 * x

/-- **Ark (Add Round Constants):** Adds pre-computed round constants to every
    element of the state vector at a given round offset

    Mirrors circomlib's `Ark(t, C, r)` -/
def ark (state C : List (F p)) (r : ℕ) : List (F p) :=
  state.mapIdx (fun i s ↦ s + C[i + r]!)

/-- **Mix (MDS matrix multiplication):** Multiplies the state vector by a
    Maximum Distance Separable matrix

    Mirrors circomlib's `Mix(t, M)` template: `out[i] = Σⱼ M[j][i] · in[j]` -/
def mix (state : List (F p)) (M : List (List (F p))) : List (F p) :=
  state.mapIdx (fun (i : ℕ) _ ↦
    (state.zipWith (fun (sj : F p) (row : List (F p)) ↦ row[i]! * sj) M).sum)

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
def mixLast (state : List (F p)) (M : List (List (F p))) (s : ℕ) : F p :=
  (state.zipWith (fun (sj : F p) (row : List (F p)) ↦ row[s]! * sj) M).sum

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
  (sorry : (1 + (t - 1) = t)) ▸ (#v[dotProduct base] ++ tail base)
where
  /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
  @[simpPoseidon]
  dotProduct (base : ℕ) : F p :=
    let s' : Vector _ t := (sorry : min (base + t) s - base = t) ▸ S.extract base (base+t)
    (state.zipWith (· * ·) s').sum
  /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` for `i ∈ [1, t)` -/
  @[simpPoseidon]
  tail (base : ℕ) : Vector (F p) (t-1) :=
    (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]! * S[base + t + i]!)

/-
mixS (m n : ℕ) (v : Vector α m) : Vector α n := _

poseidon {m n} ... := do
  let res := mixS m n
  _
-/

set_option trace.Clap.Compiler true

-- open Clap.Poseidon.Constant.C Clap.Poseidon.Constant Clap.Poseidon.Constant.M Clap.Poseidon.Constant.P Clap.Poseidon.Constant.S Clap.Poseidon
-- attribute [simpPoseidon]
--   bind pure bind_assoc
--     Option.bind_some Option.bind_assoc Option.getD_some Option.getD_none
--     id_eq getElem!_pos getElem!_neg getElem?_pos getElem?_neg

--     List.getElem_cons_succ List.getElem_cons_zero List.getElem?_cons_succ
--     List.length_cons List.length_nil
--     List.map_cons List.map_nil List.map_id_fun
--     List.mapIdx_nil List.mapIdx_mapIdx List.mapIdx_cons
--     List.mapM_nil List.mapM_cons
--     List.foldl_cons List.foldl_nil
--     List.foldlM_nil List.foldlM_cons
--     List.drop_one List.drop_succ_cons List.drop_zero
--     List.cons_append List.nil_append
--     List.reduceRange
--     List.zipWith_cons_cons List.zipWith_nil_right
--     List.tail_cons List.tail_nil
--     List.sum_cons List.sum_nil
--     List.take_succ_cons List.take_zero
--     List.set_cons_succ List.set_cons_zero

--     Nat.ofNat_pos Nat.add_one_sub_one Nat.one_lt_ofNat
--     Nat.reduceDiv Nat.reduceMul Nat.reduceLT Nat.reduceAdd Nat.reduceSub

--     one_mul add_zero zero_lt_one add_lt_iff_neg_right
--     not_lt_zero not_false_eq_true mul_zero mul_one lt_self_iff_false
--     zero_tsub zero_mul zero_add

--     List.sum

--     Function.comp_apply

-- set_option Clap.Compiler.cimplolIdentity false in
-- def mixS :=
--   cimplol(mixS_raw_5, Primes.bn254, simpPoseidon)

-- #print mixS


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
def poseidonEx (nOuts : ℕ) (inputs : List (F p)) (initState : F p)
    (C S : List (F p)) (M P : List (List (F p))) : Option (List (F p)) := do
  -- Poseidon parameters (from circomlib's PoseidonEx template)
  -- N_ROUNDS_P[t-2] for t ∈ [2, 17]
  let N_ROUNDS_P : List ℕ := [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
  let t : ℕ := inputs.length + 1
  let nRoundsF : ℕ := 8
  let nRoundsP : ℕ := N_ROUNDS_P[t - 2]!
  let half : ℕ := nRoundsF / 2

  -- initial state: [initState, inputs[0], …, inputs[nInputs−1]]
  let state := ark ([initState] ++ inputs) C 0

  -- Phase 1: first-half full rounds (r = 0 … half−2), mix with M
  let state ← (List.range (half - 1)).foldlM (fun state r ↦ do
    let l ← state.mapM sigma
    mix (ark l C ((r + 1) * t)) M) state

  -- Boundary round (r = half−1): sigma → ark → mix with P
  let state := mix (ark (← state.mapM sigma) C (half * t)) P

  let S : Vector (F p) 285 := Vector.mk (List.toArray S) (by sorry)
  let state : Vector (F p) t := Vector.mk (List.toArray state) (by sorry)
  -- Phase 2: partial rounds
  let state ← (List.range nRoundsP).foldlM (fun state r ↦ do
    let s0 := (← sigma state[0]!) + C[(half + 1) * t + r]!
    mixS r (state.set 0 s0) S) state
  let state : List (F p) := state.toArray.toList

  -- Phase 3: second-half full rounds (r = 0 … half−2), mix with M
  let state ← (List.range (half - 1)).foldlM (fun state r ↦ do
    let l ← state.mapM sigma
    mix (ark l C ((half + 1) * t + nRoundsP + r * t)) M) state

  -- Final round: sigma on all, then extract nOuts elements via MixLast
  let state ← state.mapM sigma
  (List.range nOuts).map (mixLast state M)

/-- **Poseidon:** Single-output Poseidon hash. Wraps `poseidonEx` with
    `nOuts = 1` and `initialState = 0`, returning the first element of
    the permutation output.

    Mirrors circomlib's `Poseidon(nInputs)` template. -/
def poseidon (inputs : List (F p)) (C S : List (F p)) (M P : List (List (F p))) : Option (F p) := do
  (← poseidonEx 1 inputs 0 C S M P)[0]!

section Poseidon254

open Primes

def liftArr (xs : List (ZMod p)) : List (F p) := xs.map const
def liftMat (xs : List (List (ZMod p))) : List (List (F p)) := xs.map (·.map const)

def poseidonBN254 (inputs : List (F bn254)) : Option (F bn254) :=
  let t := inputs.length + 1 -- element 2 is at list index 0 and so on
  let C := Clap.Poseidon.Constant.C[t-2]!
  let S := Clap.Poseidon.Constant.S[t-2]!
  let M := Clap.Poseidon.Constant.M[t-2]!
  let P := Clap.Poseidon.Constant.P[t-2]!
  poseidon inputs (liftArr C) (liftArr S) (liftMat M) (liftMat P)

end Poseidon254

end Clap.Poseidon

namespace Poseidon.Test

abbrev p := Primes.bn254

open Clap Lang Core
open Clap Lang ZMod
open Clap Poseidon

/-- Run poseidon on `ZMod bn254` inputs, looking up constants by `t`. -/
def testPoseidon (inputs : Vector (ZMod p) 2) (expected : F p) : Option Unit := do
  F.assert_eq (← poseidonBN254 inputs.toList) expected

--#eval! (poseidonBN254 [1,2]).get!

open Lean Meta Lean.Elab in
open Clap Compiler in
#eval show TermElabM _ from do
  let target := `Poseidon.Test.testPoseidon
  let toBeReduced := [(`testPoseidon,0,`simpAll), (`mixS,2,`simpAll)]
  let e := ((←getEnv).find? target).get!.value!
  let e ← unfoldSimplified toBeReduced target #[Expr.const `x [], .const `y []] e
  let e ← simplify `simpAll e
  logInfo m!"{e}"

-- -- circomlib test vector: hash([1, 2]) with t=3
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L50
-- example : testPoseidon
--   [1, 2] 7853200120776062878684798364095072458815029376092732009249414926327459813530
--   = some () := by native_decide

-- -- circomlib test vector: hash([3, 4]) with t=3
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L60
-- example : testPoseidon
--   [3, 4] 14763215145315200506921711489642608356394854266165572616578112107564877678998
--   = some () := by native_decide

-- -- circomlib test vector: hash([1, 2, 0, 0, 0]) with t=6
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L29
-- example : testPoseidon
--   [1, 2, 0, 0, 0] 1018317224307729531995786483840663576608797660851238720571059489595066344487
--   = some () := by native_decide

-- -- circomlib test vector: hash([3, 4, 5, 10, 23]) with t=6
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L39
-- example : testPoseidon
--   [3, 4, 5, 10, 23] 13034429309846638789535561449942021891039729847501137143363028890275222221409
--   = some () := by native_decide

end Poseidon.Test
