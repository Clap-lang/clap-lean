import Clap.Primes
import Clap.Circuit
import Clap.Sha2Ops
import Clap.Sha2
import Clap.SpecUint
import Clap.Sha2Circom

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

open Clap.Sha2.Circom

abbrev U8  : Type := FBitVec8 Primes.goldilocks
abbrev U32 : Type := FBitVec32 Primes.goldilocks

#synth Clap.Sha2.ShaU8 U8
#synth Clap.Sha2.ShaU32 U32 U8

open Clap.Sha2

-- #eval! digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc")

--#guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc") = #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

-- #guard digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") = #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]

end TestFU
