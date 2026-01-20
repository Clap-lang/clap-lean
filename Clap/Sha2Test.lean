import Clap.Sha2Ops
import Clap.Sha2

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
