import Clap.Sha2Circuit
import Clap.Sha2Cpu
import Clap.Sha2

namespace TestUInt

open Clap.Sha2

def stringToU8s (s:String) : Array UInt8 := s.toUTF8.data


#guard digest (t := Clap.Sha2.Cpu.t) (stringToU8s "abc") =
  #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

#guard digest (t := Clap.Sha2.Cpu.t) (stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]

end TestUInt

namespace TestCircuit

open Clap.Sha2
open Clap.Lang

abbrev p := Primes.goldilocks
abbrev F' := ZMod p

def stringToU8s (s:String) : Array (F8 p) :=
  let bs : Array UInt8 := s.toUTF8.data
  bs.map fun b =>
    let b : F' := (b.toNat : F')
    F8.ofF b

def testDigest (s : String) (expected : Array UInt32) : Option Unit := do
  let expected := expected.map fun u32 => F32.ofF (u32.toNat: F')
  let d := digest (t := Clap.Sha2.Circuit.t p) (stringToU8s s)
  for (d,e) in d.zip expected do
    F8.assert_eq d e
  return () -- TODO accept?

#guard! testDigest "abc" #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] = some ()

#guard! testDigest "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
   #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]
  = some ()

end TestCircuit
