import Clap.Sha2.Circuit
import Clap.Sha2.Cpu
import Clap.Sha2.Basic

namespace TestCpu

open Clap.Sha2

def stringToU8s (s:String) : Array UInt8 := s.toUTF8.data

example : Id.run (digest Id (t := Clap.Sha2.Cpu.t) (stringToU8s "abc")) =
  #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] := by
  native_decide

example : Id.run (digest Id (t := Clap.Sha2.Cpu.t) (stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) =
  #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1] := by
  native_decide

end TestCpu

namespace TestCircuit

abbrev p := Primes.goldilocks

open Clap.Sha2 Circuit
open Clap.Lang Core ZMod

def stringToU8s (s:String) : Array (F8 p) :=
  let bs : Array UInt8 := s.toUTF8.data
  bs.map fun b =>
    let b : F p := (b.toNat : F p)
    F8.ofF! b

private instance : Sha (t p) := Clap.Sha2.Circuit.instSha
private instance : Add32 Option (F32 p) := Clap.Sha2.Circuit.instAdd32

example : digest Option (t := Clap.Sha2.Circuit.t p) (stringToU8s "abc") =
  some #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] := by
  native_decide

example : digest Option (t := Clap.Sha2.Circuit.t p) (stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  some #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1] := by
  native_decide

end TestCircuit
