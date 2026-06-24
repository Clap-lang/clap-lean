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
-- #guard_msgs in
-- TODO investigate vector.set bug
-- To replicate, remove Vector.mapIdx processing
-- Something is instantiating arguments incorrectly
--   There is a pattern of a_2.set 0 (a_2 * _)
-- #guard_msgs in
set_option maxHeartbeats 0 in
set_option trace.Clap.Compile.simp.proc.vector_mapIdx_mk true in
set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
-- set_option trace.Clap.Compile.simp.proc.evalGround true in
#eval runOptionNTestByName `ExampruSym.testPoseidon_1_2 (extraPasses := Clap.Compiler.mkMethods #[
  (`ExampruSym.testPoseidon.eq_def, .Pre),
  (`Clap.PoseidonVec.poseidonBN254.eq_def, .Pre),
  (`Clap.PoseidonVec.poseidon.eq_def, .Pre),
  (`ExampruSym.poseidonExEqDef, .Pre),
  (`ExampruSym.sigmaEqDef, .Pre),
  (`ExampruSym.arkEqDef, .Pre),
  (`ExampruSym.mixSEqDef, .Pre),
  (`Clap.PoseidonVec.Constant.C.eq_def, .Pre)
])

end ExampruSym
