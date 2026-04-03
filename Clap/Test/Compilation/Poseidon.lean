import Clap.Lang
import Clap.Compiler.Basic
import Clap.Poseidon.Poseidon

open Clap Lang Core ZMod
open Clap Poseidon

def testPoseidon (inputs : Vector (ZMod p) 2) (expected : F p) : Option Unit := do
  F.assert_eq (← poseidonBN254 (inputs.toList.map const)) expected
  accept p

set_option pp.deepTerms.threshold 30
set_option pp.maxSteps 1000
set_option trace.Clap.Compiler.usedConstants true
set_option maxRecDepth 5000
set_option maxHeartbeats 800000
set_option trace.profiler true

attribute [local irreducible] Option.bind ZMod OfNat.ofNat instHAdd

attribute [local unfoldStuff] Clap.Lang.Core.eq0 Clap.Lang.Core.share Clap.Lang.Core.accept instCoreZMod F.assert_eq

open Clap.Poseidon.Constant.C Clap.Poseidon.Constant Clap.Poseidon.Constant.M Clap.Poseidon.Constant.P Clap.Poseidon.Constant.S Clap.Poseidon
attribute [local unfoldStuff] C02 C03 C04 C05 C06 C07 C08 C09 C10 C11 C12 C13 C14 C15 C16 C17 C M P S M02 M03 M04 M05 M06 M07 M08 M09 M10 M11 M12 M13 M14 M15 M16 M17 P02 P03 P04 P05 P06 P07 P08 P09 P10 P11 P12 P13 P14 P15 P16 P17 S02 S03 S04 S05 S06 S07 S08 S09 S10 S11 S12 S13 S14 S15 S16 S17 sigma ark mix mixLast mixS poseidonEx poseidon liftArr liftMat poseidonBN254 p testPoseidon mixS.dotProduct mixS.tail

--#compile testPoseidon using Primes.bn254 iters 35
