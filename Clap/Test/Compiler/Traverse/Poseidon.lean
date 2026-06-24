import Clap.Test.Compiler.Traverse.Prelude
import Clap.PoseidonVec.Poseidon

namespace ExampruSym

abbrev p := Primes.bn254

def testPoseidon (inputs : Vector (ZMod p) 2) (expected : Clap.Lang.F p) : Option Unit := do
  let res ← Clap.PoseidonVec.poseidonBN254 inputs
  Clap.Lang.F.assert_eq res expected

def testPoseidonEqDef := testPoseidon.eq_def

def testPoseidon_1_2 : Option ℕ := do
  testPoseidon #v[1, 2] 7853200120776062878684798364095072458815029376092732009249414926327459813530
  return 1

def testPoseidon_1_2EqDef := testPoseidon_1_2.eq_def
def poseidonBN254EqDef {n: ℕ} (inputs) := (@Clap.PoseidonVec.poseidonBN254.eq_def n inputs)
def poseidonEqDef {n c s} := @Clap.PoseidonVec.poseidon.eq_def n c s
def poseidonExEqDef {n c s} := @Clap.PoseidonVec.poseidonEx.eq_def n c s
def sigmaEqDef := Clap.PoseidonVec.sigma.eq_def
def arkEqDef {t c : ℕ} := @Clap.PoseidonVec.ark.eq_def t c
def mixSEqDef := @Clap.PoseidonVec.mixS.eq_def

-- TODO investigate vector.set bug
-- To replicate, remove Vector.mapIdx processing
-- Something is instantiating arguments incorrectly
--   There is a pattern of a_2.set 0 (a_2 * _)
-- #guard_msgs in
set_option maxHeartbeats 0 in
set_option trace.Clap.Compile.simp.proc.vector_mapIdx_mk true in
set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName `ExampruSym.testPoseidon_1_2 (extraPasses := Clap.Compiler.SymSets.mkMethods #[
  (`ExampruSym.testPoseidon_1_2EqDef, .Pre),
  (`ExampruSym.testPoseidonEqDef, .Pre),
  (`ExampruSym.poseidonBN254EqDef, .Pre),
  (`ExampruSym.poseidonEqDef, .Pre),
  (`ExampruSym.poseidonExEqDef, .Pre),
  (`ExampruSym.sigmaEqDef, .Pre),
  (`ExampruSym.arkEqDef, .Pre),
  (`ExampruSym.mixSEqDef, .Pre),
])

-- def vector_set (a_2) := @Vector.set (ZMod Primes.bn254) (1 + 2) a_2 0
--   (a_2 *
--     ((Vector.mapIdx (fun i s => s + (Clap.PoseidonVec.Constant.C (1 + 2))[i + 0]!)
--             (Vector.mk { toList := [0, 1, 2] } ⋯)).set
--         0
--         (a *
--           (Vector.mapIdx (fun i s => s + (Clap.PoseidonVec.Constant.C (1 + 2))[i + 0]!)
--               (Vector.mk { toList := [0, 1, 2] } ⋯))[0]!)
--         ⋯)[0]!) (by trivial)

def a := @Option.bind (Vector (ZMod Primes.bn254) (1 + 2)) ℕ
  (List.foldlM
    (fun state r =>
      (Clap.Spec.Compiler.share (state[0] * state[0])).bind fun a =>
        (Clap.Spec.Compiler.share (a * a)).bind fun a => some (state.set 0 (a * state[0]) (by trivial)))
    (Vector.mk
      {
        toList :=
          [0 + (Clap.PoseidonVec.Constant.C (1 + 2))[0], 1 + (Clap.PoseidonVec.Constant.C (1 + 2))[1],
            2 + (Clap.PoseidonVec.Constant.C (1 + 2))[2]] }
      (by trivial))
    (List.range 20))
  fun a =>
  (Clap.Lang.F.assert_eq a[0] 7853200120776062878684798364095072458815029376092732009249414926327459813530).bind
    fun a => pure 1


end ExampruSym
/-
histoRules := #[
 (pureBindMany, (22, 0.001603)),
 (flattenBindsAny, (3, 0.001216)),
 (betaReduce, (20, 0.000913)),
 (foldlM, (1, 0.000350)),
 (getElem, (2, 0.000237)),
 (range, (1, 0.000178)),
 (set, (1, 0.000161)),
totalStepTime := 0.005848
histoSkippedRules := #[(range, (4023, 0.029366)),
 (pureBindMany, (3649, 0.028232)),
 (flattenBindsAny, (3668, 0.021655)),
 (getElem, (4025, 0.021484)),
 (append, (4026, 0.018671)),
 (set, (4023, 0.017966)),
 (foldlM, (3670, 0.017891)),
 (mapIdx, (4023, 0.016905)),
 (foldr_toArray, (4024, 0.016604)),
 (evalGround, (4024, 0.010990)),
 (betaReduce, (1429, 0.007218)),
 (Vector.sum_eq_foldr, (4024, 0.004708)),
 (zetaReduce, (1449, 0.003099))]
totalSkipTime := 0.214790
passTime := Std.HashMap.ofList [(Clap.Compiler.Pass.structural, 0.003169),
 (Clap.Compiler.Pass.functional, 0.000913),
 (Clap.Compiler.Pass.general, 0.001766)]
-/
