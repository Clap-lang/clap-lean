namespace Clap.Sha2

-- https://github.com/cryspen/hax/blob/main/examples/sha256/src/sha256.rs
/-
  Gadget implementing SHA2.
  Specification can be found at
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

  Precious test vectors can be found here under "Secure hashing".
  https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values

  Main differences wrt the specification:
  - xor3 as it can be compiled more efficiently in circuit
  - fixed-length input
  - N type (for Nat) is used for generic numerical types that are
    mapped to F
-/

structure T.{u} : Type (u+1) where
  U8  : Type u
  U32 : Type u

class Sha (t : T) where
  [i₁ : Coe Nat t.U32]
  [i₄ : Coe Nat t.U8]
  [i₂ : Coe t.U8 t.U32]
  [i₃ : Inhabited t.U32]
  [i₅ : HAdd t.U32 t.U32 t.U32]
  [i₇ : ToString t.U32]
  [i₈ : ToString t.U8]
  to_nat_be : Array t.U8 -> t.U32
  rotR       : Nat -> t.U32 -> t.U32
  shiftRight : Nat -> t.U32 -> t.U32
  xor3 : (x y z : t.U32) -> t.U32
  ch   : (x y z : t.U32) -> t.U32
  maj  : (x y z : t.U32) -> t.U32

attribute [reducible] Sha.i₁ Sha.i₂ Sha.i₃ Sha.i₄ Sha.i₅ Sha.i₇ Sha.i₈
attribute [instance] Sha.i₁ Sha.i₂ Sha.i₃ Sha.i₄ Sha.i₅ Sha.i₇ Sha.i₈

variable {t : T} [Sha t]

open Sha

def of_nat_be (x:Nat) (len:Nat) : Array (t.U8) :=
    (List.reverse (aux x len)).toArray
  where
    aux (x:Nat) (len:Nat) : List t.U8 :=
      let d : Nat := x / (2^8)
      let r : Nat := x % (2^8)
      let r : t.U8 := r -- does not wrap as r < 256
      if len=0 then [] else
      r::(aux d (len-1))

def sigma_constants : Array Nat := #[7, 18, 3, 17, 19, 10]

def sigma (c0 c1 c2 : Nat) (x : t.U32) : t.U32 :=
  Sha.xor3 (Sha.rotR c0 x)
           (Sha.rotR c1 x)
           (Sha.shiftRight c2 x)

-- Sigma_0(x) = ROTR^{d0}(x) XOR ROTR^{d1}(x) XOR SHR^{d2}(x)
def sigma_0 (x : t.U32) : t.U32 :=
  sigma sigma_constants[0]!
        sigma_constants[1]!
        sigma_constants[2]! x

-- Sigma_1(x) = ROTR^{d3}(x) XOR ROTR^{d4}(x) XOR SHR^{d5}(x)
def sigma_1 (x : t.U32) : t.U32 :=
  sigma sigma_constants[3]!
        sigma_constants[4]!
        sigma_constants[5]! x

def sum_constants : Array Nat := #[2, 13, 22, 6, 11, 25]

def sum (c0 c1 c2 : Nat) (x : t.U32) : t.U32 :=
  Sha.xor3 (Sha.rotR c0 x)
           (Sha.rotR c1 x)
           (Sha.rotR c2 x)

-- Sum_0(x) = ROTR^{c0}(x) XOR ROTR^{c1}(x) XOR ROTR^{c2}(x)
def sum_0 (x : t.U32) : t.U32 :=
  sum sum_constants[0]!
      sum_constants[1]!
      sum_constants[2]! x

-- Sum_1(x) = ROTR^{c3}(x) XOR ROTR^{c4}(x) XOR ROTR^{c5}(x)
def sum_1 (x : t.U32) : t.U32 :=
  sum sum_constants[3]!
      sum_constants[4]!
      sum_constants[5]! x

def BLOCK_SIZE : Nat := 16
def LEN_SIZE : Nat := 8
def K_SIZE : Nat := 64
def HASH_SIZE : Nat := 256 / 8

abbrev Sha256Digest (u8 : Type) : Type :=  Array u8 -- HASH_SIZE
abbrev RoundConstantsTable (u32 : Type) : Type := Array u32 -- K_SIZE
abbrev Block (u32 : Type) : Type := Array u32 -- BLOck_size
abbrev Hash  (u32 : Type) : Type := Array u32 -- LEN_SIZE

def round_constants_224_256 : RoundConstantsTable Nat :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initial_hash : Hash t.U32 :=
  Array.map Coe.coe
   #[0x6a09e667,
     0xbb67ae85,
     0x3c6ef372,
     0xa54ff53a,
     0x510e527f,
     0x9b05688c,
     0x1f83d9ab,
     0x5be0cd19]

-- Section 5.1.1
-- #[hax_lib::requires((msg.len() as u64) < 0x1fffffffffffffff)]
def padding (msg : Array t.U8) : Array t.U8 :=
  let l := (msg.size + 9) % 64
  let k_zero_bytes : Array t.U8 :=
    let n_zero_bytes := 64 - l
    Array.replicate n_zero_bytes (Coe.coe 0)
  let k_one_byte : t.U8 := Coe.coe 128 -- one byte with a single 1 as msb
  let l := of_nat_be (msg.size*8) 8
  msg ++ #[k_one_byte] ++ k_zero_bytes ++ l

-- result size 16
def parse_u32 (msg : Array t.U8) : Array t.U32 :=
  assert! (msg.size == 64)
  aux 0 #[]
where
  aux (start:Nat) (acc : Array t.U32) : Array t.U32 :=
    let u32 : t.U32 := Sha.to_nat_be (Array.extract msg start (stop:=start+4))
    let acc := acc.push u32
    if start >= msg.size-4
    then assert! (acc.size = 16) ; acc
    else aux (start+4) acc

-- Section 5.2
-- result is an array of size N, containg arrays of size 16, containing 32 bit words
def parse_blocks (msg : Array t.U8) : Array (Block t.U32) :=
  aux 0 #[]
where
  aux (start : Nat) (acc : Array (Block t.U32)) : Array (Block t.U32) :=
    let block : Array t.U8 := Array.extract msg start (stop:=start+64)
    let acc := acc.push (parse_u32 block)
    if start >= msg.size-64
    then acc
    else aux (start+64) acc

-- Section 6.2.2 step 1
def schedule (block : Block t.U32) : RoundConstantsTable t.U32 :=
  aux block 16
where
  aux (acc : Array t.U32) (i:Nat) : Array t.U32 :=
    if i >= K_SIZE then acc else
    let t16 := acc[i - 16]!
    let t15 := acc[i - 15]!
    let t7 := acc[i - 7]!
    let t2 := acc[i - 2]!
    let acc := acc.push ((sigma_1 t2) +  t7 +
                         (sigma_0 t15) + t16)
    aux acc (i+1)

-- Section 6.2.2 step 3
def shuffle_i (ws:RoundConstantsTable t.U32) (hash: Hash t.U32) (i:Nat) : Hash t.U32 :=

  let a := hash[0]!
  let b := hash[1]!
  let c := hash[2]!
  let d := hash[3]!
  let e := hash[4]!
  let f := hash[5]!
  let g := hash[6]!
  let h := hash[7]!

  let t1 := h + (sum_1 e) + (Sha.ch e f g) + round_constants_224_256[i]! +
            ws[i]!
  let t2 := sum_0 a + Sha.maj a b c

  let h := g
  let g := f
  let f := e
  let e := d + t1
  let d := c
  let c := b
  let b := a
  let a := t1 + t2

  #[a, b, c, d, e, f, g, h]

def shuffle (ws:RoundConstantsTable t.U32) (hash: Hash t.U32) : Hash t.U32 :=
  aux hash 0
where
  aux hash (i:Nat) :=
    if i>=64 then hash else
    let hash := shuffle_i ws hash i
    aux hash (i+1)

def compress (block : Block t.U32) (hash : Hash t.U32) : Hash t.U32 :=
  let ws := schedule block
  let hash' := shuffle ws hash
  -- Section 6.2.2 step 4
  Array.zipWith (· + ·) hash' hash

-- TODO this should return Sha256digest
def digest (msg : Array t.U8) : Hash t.U32 :=
  let blocks := padding msg
  let blocks := parse_blocks blocks
  process_blocks blocks initial_hash 0
where
  process_blocks (blocks : Array (Block t.U32)) (acc : Hash t.U32) i :=
    if i >= blocks.size then acc else
    let acc := compress blocks[i]! acc
    process_blocks blocks acc (i+1)

end Clap.Sha2
