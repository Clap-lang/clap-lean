import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.Combinators.mapM
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
import Clap.Lang.Data.Base64Len.base64UrlDecode
import Clap.Lang.Data.Base64Len.base64UrlDecodedLength
import Clap.Lang.Data.Base64Len.base64UrlLookup
import Clap.Lang.Data.BigInt.bigLessThan
import Clap.Lang.Data.F8.F8
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Data.FArray.and
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Data.FArray.arraySelectorComplex
import Clap.Lang.Data.FArray.assert_eq
import Clap.Lang.Data.FArray.bits2num
import Clap.Lang.Data.FArray.default
import Clap.Lang.Data.FArray.eq
import Clap.Lang.Data.FArray.leftArraySelector
import Clap.Lang.Data.FArray.ofBitVec
import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.rightArraySelector
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.singleOneArray
import Clap.Lang.Data.FArray.sum
import Clap.Lang.Data.FArray.xor
import Clap.Lang.Data.FArray.xorScan
import Clap.Lang.Data.FArray.zeroExtend
import Clap.Lang.Data.FBitVec.assert_eq
import Clap.Lang.Data.FBitVec.binSum
import Clap.Lang.Data.FBitVec.eq
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.FString.assertIsAsciiDigits
import Clap.Lang.Data.FString.assertIsConcatenation
import Clap.Lang.Data.FString.isPaddedOf
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FString.ofString
import Clap.Lang.Data.FVec.assert_eq
import Clap.Lang.Data.FVec.eq
import Clap.Lang.Data.FVec.powers
import Clap.Lang.Data.HashToField.hash64BitLimbsToField
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.HashToField.hashElemsToField
import Clap.Lang.Data.HashToField.transcript
import Clap.Lang.Data.JWT.bracketsMap
import Clap.Lang.Data.Packing.assertIs64BitLimbs
import Clap.Lang.Data.Packing.assertIsBytes
import Clap.Lang.Data.Packing.bigEndianBits2Num
import Clap.Lang.Data.Packing.bigEndianBitsToScalars
import Clap.Lang.Data.Packing.bytes2BigEndianBits
import Clap.Lang.Data.Packing.chunksToFieldElem
import Clap.Lang.Data.Packing.chunksToFieldElems
import Clap.Lang.Data.Packing.num2BigEndianBits
import Clap.Lang.Data.RSA.fpPow65537Mod
import Clap.Lang.Data.RSA.fpSquareN
import Clap.Lang.Data.RSA.rsa2048e65537Pkcs1v15Verify
import Clap.Lang.Data.RSA.rsaPkcs1v15Verify
import Clap.Lang.Data.Widths
import Clap.Lang.Gate.eq0
import Clap.Lang.Gate.fpmul
import Clap.Lang.Gate.isZero
import Clap.Lang.Gate.num2bits
import Clap.Lang.Gate.share
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Poseidon.Poseidon


/-!
# The CLAP gadget library

Circuits written in `ClapM p`, each with a `convertsM` lemma saying what it computes and what
it constrains. Four layers, and every import crosses them downwards only:

- `Gate/` — the eDSL gate wrappers. A thin `def` over a gate from
  [Clap/Model/eDSL.lean](../Model/eDSL.lean), plus its
  `wellFormed` / `converts` / `constraints` / `convertsM` family, for all five gates (`eq0`,
  `share`, `isZero`, `num2bits`, `fpmul`). `fpmul.lean` also defines `Limbs.conversion`, the
  bignum-as-natural-number reading its result and the RSA gadgets are stated in.
- `Core/` — the language itself: field arithmetic, booleans, assertions, and the iteration
  combinators. Never imports `Poseidon/` or `Data/`.
- `Poseidon/` — the Poseidon hash over `bn254`, its constants, and `Computes`: all the library
  assumes of it. Never imports `Data/`.
- `Data/` — containers: bit arrays, bit vectors, field vectors, strings, bytes, the fixed-width
  `FBV8` / `F32` / `F64` wrappers, hash-to-field (`HashToField/`), the Fiat–Shamir string
  checks (`FString/isSubstring`, `FString/assertIsConcatenation`), bignum comparison
  (`BigInt/`) and RSA signature verification (`RSA/`, with the PKCS#1 v1.5 encoded
  message in `RSA/PKCS1.lean`), with their completeness and soundness lemmas.

Lang may import `Clap/RandomOracle/` and `Clap/FiatShamir/`, which sit below it: the random
oracle, and the polynomial algebra of the Fiat–Shamir checks. Neither imports anything from Lang.

Register every new gadget file here, in alphabetical position. This is the only index —
[Clap.lean](../../Clap.lean) imports this file rather than listing gadgets itself.

See [docs/specifying-circuits.md](../../docs/specifying-circuits.md).
-/
