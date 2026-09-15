import Clap.eDSLState.Convert.Base
import Clap.eDSLState.Convert.Specialised
import Clap.eDSLState.HashCons.CacheExpr
import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.HashCons.HashConsM
import Clap.eDSLState.HashCons.HashConsSt
import Clap.eDSLState.Circuit
import Clap.eDSLState.CircuitEvalSt
import Clap.eDSLState.ConstraintSystem.eq0
import Clap.eDSLState.ConstraintSystem.fpMul
import Clap.eDSLState.ConstraintSystem.isZero
import Clap.eDSLState.ConstraintSystem.num2bits
import Clap.eDSLState.ConstraintSystem.share
import Clap.eDSLState.ConstraintSystem.toCs
import Clap.eDSLState.eDSL
import Clap.eDSLState.Expr
import Clap.eDSLState.Gate
import Clap.eDSLState.IsValid
import Clap.eDSLState.Monad
-- import Clap.eDSLState.Plan -- TODO(probably Discard)
import Clap.eDSLState.Test
import Clap.eDSLState.Varstore
import Clap.eDSLState.Wheels
import Clap.eDSLState.WitnessGenerator.eq0
import Clap.eDSLState.WitnessGenerator.fpMul
import Clap.eDSLState.WitnessGenerator.isZero
import Clap.eDSLState.WitnessGenerator.num2bits
import Clap.eDSLState.WitnessGenerator.share
import Clap.eDSLState.WitnessGenerator.toWg

import Clap.Lang.F.Extensions
import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkF
import Clap.Lang.F.mkMul
import Clap.Lang.F.mkSub
import Clap.Lang.F.Tactics
import Clap.Lang.FArray.OneHotRaw
import Clap.Lang.FArray.singleOneArray
import Clap.Lang.FArray.sum
import Clap.Lang.FB.and
import Clap.Lang.FB.assert
import Clap.Lang.FB.eq
import Clap.Lang.FB.isZero
import Clap.Lang.FB.not
import Clap.Lang.FUnit.assert_eq
import Clap.Lang.FUnit.eq0

import Clap.Lang.Wheels

/-
Goodbye, sweet prince.

import Clap.Compiler.Basic
import R1Serialize.R1CS
import Clap.Primes
import Clap.Circuit
import Clap.Simulation
import Clap.Compilation
import Clap.Id
import Clap.Cfold
import Clap.Unshare
import Clap.Dedup
import Clap.Spec
import Clap.Lang
import Clap.Lang.All
import Clap.Wheels
import Clap.Milestone
import Clap.FString
import Clap.HashToField
import Clap.JWT
import Clap.Sha2.Basic
import Clap.Sha2.Cpu
import Clap.Sha2.Circuit
import Clap.Sha2.Test
import Clap.Packing
import Clap.Base64Len
import Clap.Array
import Clap.Keyless
import Clap.RSA
import Clap.Compiler.Basic
import Clap.Compiler.Deep
import Clap.Quadratic
import Clap.Test.Wheels
import Clap.Test.Compiler.Serialise
import Clap.Test.Compiler.Curry
import Clap.Test.Compiler.ToDeep
import Clap.Test.Compiler.ToWg
import Clap.Test.Compiler.Compile
import Clap.Test.Integration

-/
