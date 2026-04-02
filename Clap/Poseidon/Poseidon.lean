import Clap.Primes
import Clap.Spec
import Clap.Lang
import Clap.Poseidon.Constant
import Clap.Compiler.Basic
import Clap.Compiler.Wheels
import Clap.Primes

namespace Clap.Poseidon

open Clap Lang

abbrev p := Primes.bn254

variable [Core p] -- not a concrete instance

open Core

/-- **Sigma (S-box):** The sole source of nonlinearity in the Poseidon permutation

    Mirrors circomlib's `Sigma` template -/ 
@[unfoldStuff] def sigma (x : F p) : F p := -- 1 + 2 * 3 + 4
  let x2 := share (x * x)
  let x4 := share (x2 * x2)
  x4 * x -- sigma[1] (1 + 2 * 3 + 4)[4]
         -- share (share x[4] * x[4] * x[4] * x[4]) * x[4]
         -- 20
         -- sigma (1 + 2 * 3 + 4)
         -- sigma x → eq0 0; eq0 1; eq0 2; eq0 3; eq0 4
         -- f (sigma)
         -- f (α) → eq0 α; eq0 α
         -- f (eq0 input₁; eq0 1; eq0 2; eq0 3; eq0 4) ->
         -- eq0 0; eq0 1; eq0 2; eq0 3; eq0 4; eq0 0; eq0 1; eq0 2; eq0 3; eq0 4 -- prog₁ : original_inputs → Unit
         -- f (sigma') → eq0 0; eq0 1; eq0 2; eq0 3; eq0 4 -- prog₂ : some_state → original_inputs → Unit
  

/-- **Ark (Add Round Constants):** Adds pre-computed round constants to every
    element of the state vector at a given round offset

    Mirrors circomlib's `Ark(t, C, r)` -/
@[unfoldStuff] def ark (state C : List (F p)) (r : ℕ) : List (F p) :=
  state.mapIdx (fun i s ↦ s + C[i + r]!)

/-- **Mix (MDS matrix multiplication):** Multiplies the state vector by a
    Maximum Distance Separable matrix

    Mirrors circomlib's `Mix(t, M)` template: `out[i] = Σⱼ M[j][i] · in[j]` -/
@[unfoldStuff] def mix (state : List (F p)) (M : List (List (F p))) : List (F p) :=
  state.mapIdx (fun (i : ℕ) _ ↦
    (state.zipWith (fun (sj : F p) (row : List (F p)) ↦ row[i]! * sj) M).sum)

-- TODO: Imperative or functional style?
-- @[unfoldStuff] def mix (state : Array (F p)) (m : Array (Array (F p))) : Array (F p) := Id.run do
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
@[unfoldStuff] def mixLast (state : List (F p)) (M : List (List (F p))) (s : ℕ) : F p :=
  (state.zipWith (fun (sj : F p) (row : List (F p)) ↦ row[s]! * sj) M).sum

-- TODO: Imperative or functional style?
-- @[unfoldStuff] def mixLast (s : ℕ) (state : Array (F p)) (m : Array (Array (F p))) : F p := Id.run do
--   let mut acc : F p := 0
--   for j in [:state.size] do
--     acc := acc + (m[j]!)[s]! * state[j]!
--   return acc

/-- **MixS (Sparse Mix):** Applies the sparse-matrix multiplication used during
    partial rounds

    Mirrors circomlib's `MixS(t, S, r)` template -/
@[unfoldStuff]
def mixS (r : ℕ) (state : List (F p)) (s : List (F p)) : List (F p) :=
  let t : ℕ := state.length
  let base : ℕ := (2 * t - 1) * r
  [dotProduct base] ++ tail base t
where
  /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
  @[unfoldStuff]
  dotProduct (base : ℕ) : F p :=
    (state.zipWith (· * ·) ((s.drop base).take state.length)).sum
  /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` for `i ∈ [1, t)` -/
  @[unfoldStuff]
  tail (base t : ℕ) : List (F p) :=
    (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]! * s[base + t + i]!)

-- /-- **MixS (Sparse Mix):** Applies the sparse-matrix multiplication used during
--     partial rounds

--     Mirrors circomlib's `MixS(t, S, r)` template -/
-- @[unfoldStuff] def mixS (r : ℕ) (state : List (F p)) (s : List (F p)) : List (F p) :=
--   let t : ℕ := state.length
--   let base : ℕ := (2 * t - 1) * r
--   dotProduct 2 :: tail t base -- ++ tail t base
-- where
--   /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
--   -- dotProduct (base : ℕ) : F p :=
--   --   (state.zipWith (· * ·) ((s.drop base).take state.size)).sum
--   @[unfoldStuff]
--   dotProduct (base : ℕ) : F p :=
--     state.sum
--   /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` for `i ∈ [1, t)` -/
--   @[unfoldStuff]
--   tail (base t : ℕ) : List (F p) :=
--     state
--     -- (state.drop 1).mapIdx (fun i sᵢ ↦ sᵢ + state[0]! * s[base + t + i]!)


-- theorem mixS_nil {r s} : mixS r [] s = 

-- TODO: Imperative or functional style?
-- @[unfoldStuff] def mixS (r : ℕ) (state : Array (F p)) (s : Array (F p)) : Array (F p) := Id.run do
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
@[unfoldStuff] def poseidonEx (nOuts : ℕ) (inputs : List (F p)) (initState : F p)
    (C S : List (F p)) (M P : List (List (F p))) : List (F p) :=
  -- Poseidon parameters (from circomlib's PoseidonEx template)
  -- N_ROUNDS_P[t-2] for t ∈ [2, 17]
  let N_ROUNDS_P : List ℕ := [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
  let t : ℕ := inputs.length + 1
  let nRoundsF : ℕ := 8
  -- let nRoundsP : ℕ := 57
  let nRoundsP : ℕ := N_ROUNDS_P[t - 2]!
  -- let nRoundsP : ℕ := 10
  let half : ℕ := nRoundsF / 2

  -- initial state: [initState, inputs[0], …, inputs[nInputs−1]]
  let state := ark ([initState] ++ inputs) C 0

  -- Phase 1: first-half full rounds (r = 0 … half−2), mix with M
  let state := (List.range (half - 1)).foldl (fun state r ↦
    mix (ark (state.map sigma) C ((r + 1) * t)) M) state

  -- Boundary round (r = half−1): sigma → ark → mix with P
  let state := mix (ark (state.map sigma) C (half * t)) P

  -- Phase 2: partial rounds
  let state := (List.range nRoundsP).foldl (
    fun state r ↦
      -- state.append state
      let s0 := sigma state[0]! + C[(half + 1) * t + r]!
      mixS r (state.set 0 s0) S
      -- state.append state
    ) state

  -- Phase 3: second-half full rounds (r = 0 … half−2), mix with M
  let state := (List.range (half - 1)).foldl (fun state r ↦
    mix (ark (state.map sigma) C ((half + 1) * t + nRoundsP + r * t)) M) state

  -- -- -- Final round: sigma on all, then extract nOuts elements via MixLast
  let state := state.map sigma
  (List.range nOuts).map (mixLast state M)
open Clap.Poseidon.Constant

/-- **Poseidon:** Single-output Poseidon hash. Wraps `poseidonEx` with
    `nOuts = 1` and `initialState = 0`, returning the first element of
    the permutation output.

    Mirrors circomlib's `Poseidon(nInputs)` template. -/
@[unfoldStuff] def poseidon (inputs : List (F p)) (C S : List (F p)) (M P : List (List (F p))) : F p :=
  (poseidonEx 1 inputs 0 C S M P)[0]!

section Poseidon254

open Primes

@[unfoldStuff] def liftArr (xs : List (ZMod p)) : List (F p) := xs.map const
@[unfoldStuff] def liftMat (xs : List (List (ZMod p))) : List (List (F p)) := xs.map (·.map const)

@[unfoldStuff] def poseidonBN254 (inputs : List (F bn254)) : F bn254 :=
  let t := inputs.length + 1 -- element 2 is at list index 0 and so on
  let C := Clap.Poseidon.Constant.C[t-2]!
  let S := Clap.Poseidon.Constant.S[t-2]!
  let M := Clap.Poseidon.Constant.M[t-2]!
  let P := Clap.Poseidon.Constant.P[t-2]!
  poseidon inputs (liftArr C) (liftArr S) (liftMat M) (liftMat P)

-- #eval! @poseidonBN254 ZMod.instCoreZMod [1, 2]

end Poseidon254

end Clap.Poseidon

namespace Poseidon.Test

abbrev p := Primes.bn254

open Clap Lang Core
open Clap Lang ZMod
open Clap Poseidon

/-- Run poseidon on `ZMod bn254` inputs, looking up constants by `t`. -/
@[unfoldStuff] def testPoseidon (inputs : Vector (ZMod p) 2) (expected : F p) : Option Unit := do
  F.assert_eq (← poseidonBN254 (inputs.toList.map const)) expected
  accept p

-- circomlib test vector: hash([1, 2]) with t=3
-- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L50
example : testPoseidon
  #v[1, 2] 7853200120776062878684798364095072458815029376092732009249414926327459813530
  = some () := by native_decide

-- -- circomlib test vector: hash([3, 4]) with t=3
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L60
-- example : testPoseidon
--   #v[3, 4] 14763215145315200506921711489642608356394854266165572616578112107564877678998
--   = some () := by native_decide

-- -- circomlib test vector: hash([1, 2, 0, 0, 0]) with t=6
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L29
-- example : testPoseidon
--   #v[1, 2, 0, 0, 0] 1018317224307729531995786483840663576608797660851238720571059489595066344487
--   = some () := by native_decide

-- -- circomlib test vector: hash([3, 4, 5, 10, 23]) with t=6
-- -- https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L39
-- example : testPoseidon
--   #v[3, 4, 5, 10, 23] 13034429309846638789535561449942021891039729847501137143363028890275222221409
--   = some () := by native_decide

-- @[unfoldStuff] def test {p} [Core p] (inputs : Vector (ZMod p) 2) (expected : F p) := testPoseidon inputs expected

-- dsimproc_decl listRange (List.range _) := fun e ↦ do
--   let_expr List.range k ← e | return .continue
--   let l := List.range k.nat?.get!
--   return .visit (Lean.toExpr l)

-- attribute [simproc] listRange

-- attribute [simp] C

-- example : (2 : ZMod 2) + 4 = sorry := by
--   simp +ground

-- Circuit (a b c) :
-- let part₁ := stuff
-- let part₂ := stuff' part₁
-- let part₃ := stuff'' part₂
-- part₃ a b c

-- set_option diagnostics true
-- set_option trace.Debug.Meta.Tactic.simp true
-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.Tactic.simp.all true

-- set_option pp.exprSizes false
-- set_option trace.Clap.Compiler.reduce.simplify.countHeartbeats true
-- set_option trace.Clap.Compiler.reduce.simplify.exprSizesBeforeSimplify true

-- set_option pp.deepTerms true
set_option pp.deepTerms.threshold 30
set_option pp.maxSteps 1000
-- set_option trace.Clap.Compiler true
-- set_option trace.Clap.Compiler.reduce.foldProjs false
-- set_option trace.Clap.Compiler.reduce.beta false
-- set_option trace.Clap.Compiler.reduce.letSome false
-- set_option trace.Clap.Compiler.reduce.linearise false
-- set_option trace.Clap.Compiler.reduce.unfoldAny true
-- set_option trace.Clap.Compiler.reduce.zeta false
-- set_option trace.Clap.Compiler.reduce.simplify true
-- set_option trace.Clap.Compiler.reduce.unfoldAny.const true
set_option trace.Clap.Compiler.usedConstants true
-- set_option trace.Clap.Compiler.reduce false
-- set_option maxRecDepth 5500
set_option maxHeartbeats 800000
set_option debug.skipKernelTC true

------------------------- Profiling -------------------------
-- set_option diagnostics true
-- set_option trace.profiler.threshold 40
-- set_option profiler.threshold 15
set_option trace.profiler true
-- set_option profiler true
------------------------- Profiling -------------------------

attribute [local irreducible] bind ZMod OfNat.ofNat instHAdd List.append
#check Lean.Meta.Simp.Config
-- attribute [local irreducible] mixS mix ark

-- attribute [local irreducible] ark

-- set_option Clap.Compiler.Debug true
-- set_option trace.Clap.Compiler.Debug true
-- set_option trace.Clap.Compiler.Debug.revertOnTimeout true
-- set_option trace.Clap.Compiler.Debug.revertOnTimeout true
set_option maxRecDepth 1500
-- set_option maxHeartbeats 0
-- 8.2 (together)
-- 9.7 (open)
-- 5.1 (closed)
-- 4.515127 (pure simp)
-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.Tactic.simp.all true
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.isDefEq.stuck true
-- set_option diagnostics true

attribute [instance high] List.instAppend

#compile testPoseidon using Primes.bn254 iters 35
-- Clap.Poseidon.mixS [Core Poseidon.p] (r : ℕ) (state s : Array (F Poseidon.p)) : Array (F Poseidon.p)
-- #check List.map_cons
-- /-- Run poseidon on `ZMod bn254` inputs, looking up constants by `t`. -/
-- @[unfoldStuff] def testMixS (inputs : Vector (ZMod p) 2) (expected : F p) : Option Unit := do
  
-- example : [sorry, 2, 3].map (·+2) = sorry := by
--   simp? +singlePass
--   simp +singlePass
--   simp +singlePass

-- #[dotProduct base] ++ tail base t (50 (mixS 49 (mixS 48 ...)))
-- #[sum base] ++ fold base t (50 (mixS 49 (mixS 48))) ... mixS 0 (#[1, 2, 3].set 0 0)
-- mixS 0 (Array.set #[1, 2, 3] 0 0)          -- (0 : ℕ) (Array.set #[1, 2, 3] 0 0 : Array (F p))
-- mixS 1 (mixS 0 (Array.set #[1, 2, 3] 0 0)) -- mixS : _ → _ → F
-- are you a function?
-- notVerboten
-- args - not functions | field elements | vectors of field elements
-- #[sum base] ++ fold base t (50 (mixS 49 (mixS 48))) ... mixS 0 (#[1, 2, 3].set 0 0)
--  #[sum base] ++ fold base t (50 (#[sum base] ++ fold base ... mixS ...
-- 

end Poseidon.Test
