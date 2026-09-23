import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.Combinators.ofFnM
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.F.dotProduct
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.ofChar
import Clap.Lang.Core.F.ofUInt8
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.assert
import Clap.Lang.Core.FB.assertBool
import Clap.Lang.Core.FB.assert_eq
import Clap.Lang.Core.FB.conditionallyAssert
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.eqBool
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Core.FB.or
import Clap.Lang.Core.FB.xor
import Clap.Lang.Core.FUnit.assert_eq
import Clap.Lang.Core.FUnit.assert_range
import Clap.Lang.Core.FUnit.guardedAssertEq
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Lang.Data.F8.F8
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Data.FArray.assert_eq
import Clap.Lang.Data.FArray.bits2num
import Clap.Lang.Data.FArray.default
import Clap.Lang.Data.FArray.eq
import Clap.Lang.Data.FArray.ofBitVec
import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.singleOneArray
import Clap.Lang.Data.FArray.leftArraySelector
import Clap.Lang.Data.FArray.rightArraySelector
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.sum
import Clap.Lang.Data.FArray.xor
import Clap.Lang.Data.FArray.xorScan
import Clap.Lang.Data.FArray.zeroExtend
import Clap.Lang.Data.FBitVec.assert_eq
import Clap.Lang.Data.FBitVec.binSum
import Clap.Lang.Data.FBitVec.eq
import Clap.Lang.Data.FString.isPaddedOf
import Clap.Lang.Data.FString.ofString
import Clap.Lang.Data.FVec.eq
import Clap.Lang.Data.Widths
import Clap.Lang.Gate.eq0
import Clap.Lang.Gate.isZero
import Clap.Lang.Gate.num2bits

/-!
# The CLAP gadget library

Circuits written in `ClapM p`, each with a `convertsM` lemma saying what it computes and what
it constrains. Three layers, and every import crosses them downwards only:

- `Gate/` — the eDSL gate wrappers. A thin `def` over a gate from
  [Clap/Model/eDSL.lean](../Model/eDSL.lean), plus its
  `wellFormed` / `converts` / `constraints` / `convertsM` family. `share` and `fpmul` are
  implemented gates still waiting for a wrapper here.
- `Core/` — the language itself: field arithmetic, booleans, assertions, and the iteration
  combinators. Never imports `Data/`.
- `Data/` — containers: bit arrays, bit vectors, field vectors, strings, bytes, and the
  fixed-width `FBV8` / `F32` / `F64` wrappers.

Register every new gadget file here, in alphabetical position. This is the only index —
[Clap.lean](../../Clap.lean) imports this file rather than listing gadgets itself.

See [docs/specifying-circuits.md](../../docs/specifying-circuits.md).
-/
