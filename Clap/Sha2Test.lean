import Clap.Primes
import Clap.Circuit
import Clap.Sha2Ops
import Clap.Sha2
import Clap.SpecUint

--import Init.Data.BitVec.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic -- field operations


namespace TestBitVec

abbrev U8 : Type := BitVec 8
abbrev U32 : Type := BitVec 32

instance : Coe Nat U8 where
  coe n := BitVec.ofNat 8 n

instance : Coe UInt8 U8 where
  coe n := n.toNat

instance : Coe U8 U32 where
  coe u8 := u8.toFin

open Clap.Sha2

#guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc") = #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

#guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") = #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]

end TestBitVec



namespace TestUInt

abbrev U8 : Type := UInt8
abbrev U32 : Type := UInt32

instance : Coe Nat U8 where
  coe n := UInt8.ofNat n

instance : Coe UInt8 U8 where
  coe n := n

instance : Coe U8 U32 where
  coe u8 := UInt32.ofNat u8.toNat

open Clap.Sha2

#guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc") = #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

#guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") = #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]

end TestUInt



namespace TestFU

-- TODO I should not be able to instantiate U8 with a prime and U32 with another prime
-- TODO I should not be able to instantiate U32 with a field smaller than 32bits likes babybear, or U8 with a field smaller than 8 bits

abbrev U8  : Type := ZMod Primes.goldilocks
abbrev U32 : Type := ZMod Primes.goldilocks

-- instance : Coe UInt8 U8 where
--   coe u8 := (u8.toNat : ZMod Primes.prime_goldilocks)

#synth Clap.Sha2.ShaU8 U8

-- instance {n:Nat} : OfNat U8 n where
--   ofNat := n % 2^8

-- #guard (2^8:BitVec 8) = ((2^8:UInt8):TestFU.U8)

-- instance : Coe Nat U32 where
--   coe u32 := u32 % 2^32

-- instance : Coe UInt32 U32 where
--   coe u32 := (u32.toNat : ZMod Primes.goldilocks)

-- instance : Coe (BitVec 32) U32 where
--   coe u32 := u32.toNat

-- instance {n:Nat} : OfNat U32 n where
--   --ofNat := (n % (2^32) : ZMod Primes.goldilocks)
--   ofNat := (n : ZMod Primes.goldilocks)


--#synth ∀ (n:Nat), OfNat U32 n

-- instance : Coe U8 U32 where
--   coe u8 := (u8.toNat : ZMod Primes.goldilocks)

-- instance : HAnd U32 U32 U32 where
--   hAnd a b := ((UInt32.ofNat a.val) &&& (UInt32.ofNat b.val))

-- instance : HXor U32 U32 U32 where
--   hXor a b := ((UInt32.ofNat a.val) ^^^ (UInt32.ofNat b.val))

-- instance : Complement U32 where
--   complement a := ((UInt32.ofNat a.val)).complement

-- instance : HShiftLeft U32 U32 U32 where
--   hShiftLeft a b := ((UInt32.ofNat a.val) <<< (UInt32.ofNat b.val))

-- -- TODO can we remove this or the other?
-- instance : HShiftRight U32 U32 U32 where
--   hShiftRight a b := ((UInt32.ofNat a.val) >>> (UInt32.ofNat b.val))

-- instance : HOr U32 U32 U32 where
--   hOr a b := ((UInt32.ofNat a.val) ||| (UInt32.ofNat b.val))

-- --TODO
-- instance : HAdd U32 U32 U32 where
--   hAdd a b := (a.toNat : ZMod Primes.goldilocks) +
--               (b.toNat : ZMod Primes.goldilocks)
-- instance : HSub U32 U32 U32 where
--   hSub a b := (a.toNat : ZMod Primes.goldilocks) -
--               (b.toNat : ZMod Primes.goldilocks)
-- instance : HMul U32 U32 U32 where
--   hMul a b := (a.toNat : ZMod Primes.goldilocks) *
--               (b.toNat : ZMod Primes.goldilocks)

-- instance : Inhabited U32 where
--   default := 0

-- #guard (10:BitVec 32) ^^^ (3:BitVec 32) = ((10:UInt32):TestFU.U32) ^^^ ((3:UInt32):TestFU.U32)

-- set_option pp.coercions false
-- --set_option pp.all true

-- example : (10:UInt32) >>> (3:UInt32) = (10:TestFU.U32) >>> (3:TestFU.U32) := by
--   conv_rhs => unfold HShiftRight.hShiftRight
--   unfold instHShiftRightU32
--   dsimp
--   congr 3
--   . unfold ZMod.val
--     unfold Primes.goldilocks
--     dsimp
--     unfold Fin.val
--     --unfold_projs
--     --unfold UInt32.ofNat
--     --rw [← Nat.toUInt32_eq]
--     conv_rhs =>
--       unfold OfNat.ofNat --U32 10 instOfNatU32
--     unfold instOfNatU32
--     dsimp only [Nat.cast_ofNat]
--     norm_num
--     unfold ZMod
--     dsimp only [Fin.reduceDiv] --, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
--       UInt32.reduceOfNat]


--     dsimp only [Nat.reduceAdd, Fin.reduceDiv, Fin.reduceSub, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
--       UInt32.reduceOfNat]

--     field_simp
--     ring_nf

--     --plausible

-- #exit

#guard (10:UInt32) >>> (3:UInt32) = (10:TestFU.U32) >>> (3:TestFU.U32)

#guard (10:UInt32) <<< (3:UInt32) = (10:TestFU.U32) <<< (3:TestFU.U32)

#guard (10:UInt32) ||| (3:UInt32) = (10:TestFU.U32) ||| (3:TestFU.U32)

#guard (~~~(10:UInt32)).toNat = (~~~(10:TestFU.U32)).toNat

-- TODO this test fails if TestBitvec is not commented
#guard (~~~(10:UInt32):UInt32) = (~~~(10:TestFU.U32):TestFU.U32)


#synth Clap.Sha2.ShaU32 U32 U8

open Clap.Sha2

#eval! digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc")

#guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc") = #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

-- #guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") = #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]

end TestFU
