import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Tests

def testCache : HashConsSt 47 where
  exprs := #[
    .v 0, -- 0
    .v 1, -- 1 
    .v 2, -- 2
    .binary_op 0 1 .add, -- 3
    .binary_op 3 2 .sub, -- 4
    .v 3 -- 5
  ]
  wellFormed := by decide

-- NOTE this is a bad example and I'm only doing it like this because the monad doesn't work yet
def testCircuit : Circuit := #[
  .isZero 4, -- (.v 0 + .v 1) - .v 2
  .eq0 5 -- .v 2 ≠ .v 0 + .v 1
]
def testCs := testCircuit.toCs testCache 3
def testWg := testCircuit.toWg testCache 3
def inputs : Array (Vector (ZMod 47) 3) := #[
  #v[0,0,0],
  #v[0,1,0],
  #v[0,2,0],
  #v[1,0,0],
  #v[1,1,0],
  #v[1,2,0],
  #v[2,0,0],
  #v[2,1,0],
  #v[2,2,0],
  #v[0,0,1],
  #v[0,1,1],
  #v[0,2,1],
  #v[1,0,1],
  #v[1,1,1],
  #v[1,2,1],
  #v[2,0,1],
  #v[2,1,1],
  #v[2,2,1],
  #v[0,0,2],
  #v[0,1,2],
  #v[0,2,2],
  #v[1,0,2],
  #v[1,1,2],
  #v[1,2,2],
  #v[2,0,2],
  #v[2,1,2],
  #v[2,2,2],
]

instance : Fact (Nat.Prime 47) := ⟨by norm_num⟩

def witnesses := inputs.map (λ x => testWg.run x)
def evaluations := witnesses.map (λ x => testCs.run x)
def wellbehaved := (inputs.zip witnesses).map (λ (x,y) => x.toArray.isPrefixOf y) |>.all (.)
def satisfiable := inputs.map (λ x => x[0]! + x[1]! != x[2]!)
def complete := satisfiable.zip evaluations |>.map (λ (s, e) => !s || e) |>.all (.)
def sound := satisfiable.zip evaluations |>.map (λ (s, e) => s || !e) |>.all (.) --special case

def results := witnesses.zip evaluations

/-!
The three properties `Plan.lean` set out as the back end's obligations, checked on this
circuit. They are `#guard`ed rather than `#eval`ed so that a regression fails the build.

These are smoke tests over one 2-gate circuit, not proofs; the real evidence is the `convertsM`
lemmas in `Clap/Lang/`.
-/

#guard wellbehaved
#guard complete
#guard sound

end Clap.Tests
