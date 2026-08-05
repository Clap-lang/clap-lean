import Clap.eDSLState.ConstraintSystem
import Clap.eDSLState.WitnessGenerator

namespace Clap.Tests

def testCache : HashConsSt 47 where
  exprs := #[
    .v 0,
    .v 1,
    .v 2,
    .binary_op 0 1 .add,
    .binary_op 3 2 .sub,
    .v 4
  ]
  wellFormed := by decide

-- NOTE this is a bad example and I'm only doing it like this because the monad doesn't work yet
def testCircuit : Circuit 47 := #[
  .isZero 4,
  .eq0 5
]

def testCs := testCircuit.toCs testCache 3
def testWg := testCircuit.toWg testCache
def inputs : Array (Array (ZMod 47)) := #[
  #[0,0,0],
  #[0,1,0],
  #[0,2,0],
  #[1,0,0],
  #[1,1,0],
  #[1,2,0],
  #[2,0,0],
  #[2,1,0],
  #[2,2,0],
  #[0,0,1],
  #[0,1,1],
  #[0,2,1],
  #[1,0,1],
  #[1,1,1],
  #[1,2,1],
  #[2,0,1],
  #[2,1,1],
  #[2,2,1],
  #[0,0,2],
  #[0,1,2],
  #[0,2,2],
  #[1,0,2],
  #[1,1,2],
  #[1,2,2],
  #[2,0,2],
  #[2,1,2],
  #[2,2,2],
]
def witnesses := inputs.map (λ x => testWg.run x)
def evaluations := witnesses.map (λ x => testCs.run x)
def wellbehaved := (inputs.zip witnesses).map (λ (x,y) => x.isPrefixOf y) |>.all (.)
def satisfiable := inputs.map (λ x => x[0]! + x[1]! != x[2]!)
def complete := satisfiable.zip evaluations |>.map (λ (s, e) => !s || e) |>.all (.)
def sound := satisfiable.zip evaluations |>.map (λ (s, e) => s || !e) |>.all (.) --special case

def results := witnesses.zip evaluations

#eval results
#eval wellbehaved
#eval complete
#eval sound

#eval testWg.run #[1,1,2]

end Clap.Tests
