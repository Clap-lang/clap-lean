import Clap.Wheels

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

class U32Monadic (m : Type → Type) [Monad m] (t : Type) where
  add32 : t → t → m t
  xor3 : (x y z : t) -> m t
  maj  : (x y z : t) -> m t

class Sha (t : T) where
  [i₁ : Coe Nat t.U8]
  [i₂ : Coe Nat t.U32]
  [i₃ : Coe t.U8 t.U32]
  [i₄ : Inhabited t.U32]
  [i₅ : ToString t.U8]
  [i₆ : ToString t.U32]
  to_nat_be  : Vector t.U8 4 → t.U32
  rotR       : Nat -> t.U32 -> t.U32
  shiftRight : Nat -> t.U32 -> t.U32
  ch   : (x y z : t.U32) -> t.U32

attribute [reducible] Sha.i₁ Sha.i₂ Sha.i₃ Sha.i₄ Sha.i₅ Sha.i₆
attribute [instance] Sha.i₁ Sha.i₂ Sha.i₃ Sha.i₄ Sha.i₅ Sha.i₆

variable {m : Type → Type} [Monad m]
variable {t : T} [Sha t] [U32Monadic m t.U32]

open Sha U32Monadic

def of_nat_be (x:Nat) (len:Nat) : Vector t.U8 len :=
  aux x len
  where
    aux (x:Nat) (len:Nat) : Vector t.U8 len :=
      if h : len=0
      then h ▸ #v[]
      else
        let d : Nat := x / (2^8)
        let r : Nat := x % (2^8)
        let r : t.U8 := r -- does not wrap as r < 256
        have h : (len - 1 + 1) = len := by omega
        h ▸ ((aux d (len-1)).push r)

def sigma_constants : Array Nat := #[7, 18, 3, 17, 19, 10]

def sigma (c0 c1 c2 : Nat) (x : t.U32) : m t.U32 :=
  xor3
    (rotR c0 x)
    (rotR c1 x)
    (shiftRight c2 x)

-- Sigma_0(x) = ROTR^{d0}(x) XOR ROTR^{d1}(x) XOR SHR^{d2}(x)
def sigma_0 (x : t.U32) : m t.U32 :=
  sigma
    sigma_constants[0]!
    sigma_constants[1]!
    sigma_constants[2]!
    x

-- Sigma_1(x) = ROTR^{d3}(x) XOR ROTR^{d4}(x) XOR SHR^{d5}(x)
def sigma_1 (x : t.U32) : m t.U32 :=
  sigma
    sigma_constants[3]!
    sigma_constants[4]!
    sigma_constants[5]!
    x

def sum_constants : Array Nat := #[2, 13, 22, 6, 11, 25]

def sum (c0 c1 c2 : Nat) (x : t.U32) : m t.U32 :=
  xor3
    (rotR c0 x)
    (rotR c1 x)
    (rotR c2 x)

-- Sum_0(x) = ROTR^{c0}(x) XOR ROTR^{c1}(x) XOR ROTR^{c2}(x)
def sum_0 (x : t.U32) : m t.U32 :=
  sum
    sum_constants[0]!
    sum_constants[1]!
    sum_constants[2]!
    x

-- Sum_1(x) = ROTR^{c3}(x) XOR ROTR^{c4}(x) XOR ROTR^{c5}(x)
def sum_1 (x : t.U32) : m t.U32 :=
  sum
    sum_constants[3]!
    sum_constants[4]!
    sum_constants[5]!
    x

def BLOCK_SIZE : Nat := 16
def LEN_SIZE : Nat := 8
def K_SIZE : Nat := 64
def HASH_SIZE : Nat := 256 / 8

abbrev Sha256Digest (u8 : Type) : Type :=  Vector u8 32
abbrev RoundConstantsTable (u32 : Type) : Type := Vector u32 64
abbrev Block (u32 : Type) : Type := Vector u32 16
abbrev Hash  (u32 : Type) : Type := Vector u32 8

def round_constants_224_256 : RoundConstantsTable t.U32 :=
  Vector.map Coe.coe
  #v[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initial_hash : Hash t.U32 :=
  Vector.map Coe.coe
  #v[0x6a09e667,
    0xbb67ae85,
    0x3c6ef372,
    0xa54ff53a,
    0x510e527f,
    0x9b05688c,
    0x1f83d9ab,
    0x5be0cd19]

abbrev ceil n := (n+72) / 64

-- Section 5.1.1
-- #[hax_lib::requires((msg.len() as u64) < 0x1fffffffffffffff)]
--set_option maxRecDepth 1100 in
def padding {n:ℕ} (msg : Vector t.U8 n) : Vector t.U8 ((ceil n)*64) :=
  letI m := (n + 9) % 64
  let k_zero_bytes : Vector t.U8 ((64-m)%64) :=
    let n_zero_bytes := (64 - m) % 64
    Vector.replicate n_zero_bytes (Coe.coe 0)
  let k_one_byte : t.U8 := Coe.coe 128 -- one byte with a single 1 as msb
  let l : Vector t.U8 8 := of_nat_be (msg.size*8) 8
  have h : (n + 1 + (64 - m) % 64 + 8) = (ceil n) * 64 := by
    show n + 1 + (64 - (n + 9) % 64) % 64 + 8 = ((n + 72) / 64) * 64
    omega
  h ▸
  (msg ++ #v[k_one_byte] ++ k_zero_bytes ++ l)

def parse_u32 (msg : Vector t.U8 64) : Vector t.U32 16 :=
  let tmp : Vector (Vector t.U8 4) 16 := toChunks 4 msg
  tmp.map to_nat_be

-- Section 5.2
def parse_blocks {n} (msg : Vector t.U8 (n*64)) : Vector (Block t.U32) n :=
  let tmp : Vector (Vector t.U8 64) n := toChunks 64 msg
  tmp.map parse_u32

-- Section 6.2.2 step 1
partial def schedule (block : Block t.U32) : m (RoundConstantsTable t.U32) :=
  aux 16 block
where
  aux (i:Nat) (acc : Vector t.U32 i) : m (Vector t.U32 64) := do
    if h : i = 64
    then
      return h ▸ acc
    else
      let t16 := acc[i - 16]!
      let t15 := acc[i - 15]!
      let t7 := acc[i - 7]!
      let t2 := acc[i - 2]!

      let sum ← [(←sigma_1 t2), t7, (←sigma_0 t15), t16].foldlM add32 default
      let acc := acc.push sum

      aux (i+1) acc

-- Section 6.2.2 step 3
def shuffle_i (ws:RoundConstantsTable t.U32) (hash: Hash t.U32) (i:Nat) : m (Hash t.U32) := do

  let a := hash[0]!
  let b := hash[1]!
  let c := hash[2]!
  let d := hash[3]!
  let e := hash[4]!
  let f := hash[5]!
  let g := hash[6]!
  let h := hash[7]!

  let t1 ← [h, (←sum_1 e), ch e f g, round_constants_224_256[i]!, ws[i]!].foldlM add32 default
  let t2 ← [(←sum_0 a), (←maj a b c)].foldlM add32 default

  let h := g
  let g := f
  let f := e
  let e ← add32 d t1
  let d := c
  let c := b
  let b := a
  let a ← add32 t1 t2

  return #v[a, b, c, d, e, f, g, h]

def shuffle (ws:RoundConstantsTable t.U32) (hash: Hash t.U32) : m (Hash t.U32) :=
  (List.range 64).foldlM (shuffle_i ws) hash

def compress (hash : Hash t.U32) (block : Block t.U32) : m (Hash t.U32) := do
  let ws ← schedule block
  let hash' ← shuffle ws hash
  -- Section 6.2.2 step 4
  Vector.mapM (fun (a, b) ↦ add32 a b) (Vector.zip hash' hash)

-- TODO this should return Sha256digest
def digest {n:ℕ} (msg : Vector t.U8 n) : m (Hash t.U32) :=
  let blocks : Vector t.U8 ((ceil n) * 64) := padding msg
  let blocks : Vector _ (ceil n) := parse_blocks blocks
  Vector.foldlM compress initial_hash blocks

end Clap.Sha2
