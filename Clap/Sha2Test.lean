import Clap.Sha2Cpu
import Clap.Sha2

namespace TestUInt

open Clap.Sha2

def stringToU8s (s:String) : Array UInt8 :=
  let bs : ByteArray := s.toUTF8
  let bs : Array UInt8 := bs.data
  bs

#guard digest (t := Clap.Sha2.Cpu.t) (stringToU8s "abc") =
  #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

#guard digest (t := Clap.Sha2.Cpu.t) (stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]

end TestUInt
