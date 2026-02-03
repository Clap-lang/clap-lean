import Clap.Sha2Test

open Clap.Sha2.Circom

abbrev U8  : Type := FBitVec8 Primes.bn254
abbrev U32 : Type := FBitVec32 Primes.bn254

open Clap.Sha2

-- `lake exec Benchmark`
def main : IO Unit := do
  IO.println ("Start")

  let res := digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abc")
  if res = #[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]
  then IO.println ("OK") else IO.println ("KO")

  -- let res := digest (U8:=U8) (U32:=U32) (Clap.Sha2_ops.stringToU8s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
  -- if res = #[0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1]
  -- then IO.println ("OK") else IO.println ("KO")

  IO.println ("done")
