namespace Clap.Sha2

class ShaU8 (U8 : Type) where
  of_nat_be : Nat -> Nat -> Array U8
  stringToU8s : String -> Array U8

class ShaU32 (U32 : Type) (U8 : Type) where
  sum_0 : U32 -> U32
  sum_1 : U32 -> U32
  sigma_0 : U32 -> U32
  sigma_1 : U32 -> U32
  to_nat_be : Array U8 -> U32
  ch : (x y z : U32) -> U32
  maj : (x y z : U32) -> U32

variable {U8 : Type}
  [Coe UInt8 U8]
  [ShaU8 U8]

variable {U32 : Type}
  [ShaU32 U32 U8]
  [∀ (n:Nat), OfNat U32 n]
  [Coe UInt32 U32]
  [HAdd U32 U32 U32]
  [Inhabited U32]

-- https://github.com/cryspen/hax/blob/main/examples/sha256/src/sha256.rs
/-
  Gadget implementing SHA2.
  Specification can be found at
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

  Precious test vectors can be found here under "Secure hashing".
  https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values
-/

def BLOCK_SIZE : Nat := 16
def LEN_SIZE : Nat := 8
def K_SIZE : Nat := 64
def HASH_SIZE : Nat := 256 / 8

abbrev Sha256Digest (u8 : Type) : Type :=  Array u8 -- HASH_SIZE
abbrev RoundConstantsTable (u32 : Type) : Type := Array u32 -- K_SIZE
abbrev Block (u32 : Type) : Type := Array u32 -- BLOck_size
abbrev Hash  (u32 : Type) : Type := Array u32 -- LEN_SIZE

def round_constants_224_256 : RoundConstantsTable U32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initial_hash : Hash U32 :=
  #[ 0x6a09e667,
     0xbb67ae85,
     0x3c6ef372,
     0xa54ff53a,
     0x510e527f,
     0x9b05688c,
     0x1f83d9ab,
     0x5be0cd19 ]

-- Section 5.1.1
-- #[hax_lib::requires((msg.len() as u64) < 0x1fffffffffffffff)]
def padding (msg : Array U8) : Array U8 :=
  let l := (msg.size + 9) % 64
  let k_zero_bytes : Array U8 :=
    let n_zero_bytes := 64 - l
    Array.replicate n_zero_bytes (0:UInt8)
  let k_one_byte : U8 := (128:UInt8) -- one byte with a single 1 as msb
  let l := ShaU8.of_nat_be (msg.size*8) 8
  msg ++ #[k_one_byte] ++ k_zero_bytes ++ l

-- result size 16
def parse_u32 (msg : Array U8) : Array U32 :=
  aux 0 #[]
where
  aux (start:Nat) (acc : Array U32) : Array U32 :=
    let u32 : U32 := ShaU32.to_nat_be (Array.extract msg start (stop:=start+4))
    let acc := acc.push u32
    if start >= msg.size-4
    then acc
    else aux (start+4) acc

-- Section 5.2
-- result is an array of size N, containg arrays of size 16, containing 32 bit words
def parse_blocks (msg : Array U8) : Array (Block U32) :=
  aux 0 #[]
where
  aux (start : Nat) (acc : Array (Block U32)) : Array (Block U32) :=
  let block : Array U8 := Array.extract msg start (stop:=start+64)
  let acc := acc.push (parse_u32 block)
  if start >= msg.size-64
  then acc
  else aux (start+64) acc

-- Section 6.2.2 step 1
def schedule (block : Block U32) : RoundConstantsTable U32 :=
  aux block 16
where
  aux (acc : Array U32) (i:Nat) : Array U32 :=
    if i >= K_SIZE then acc else
    let t16 := acc[i - 16]!
    let t15 := acc[i - 15]!
    let t7 := acc[i - 7]!
    let t2 := acc[i - 2]!
    let acc := acc.push ((ShaU32.sigma_1 (U32:=U32) (U8:=U8)  t2) +  t7 +
                         (ShaU32.sigma_0 (U32:=U32) (U8:=U8) t15) + t16)
    aux acc (i+1)

-- Section 6.2.2 step 3
def shuffle_i (ws:RoundConstantsTable U32) (hash: Hash U32) (i:Nat) : Hash U32 :=

  let a := hash[0]!
  let b := hash[1]!
  let c := hash[2]!
  let d := hash[3]!
  let e := hash[4]!
  let f := hash[5]!
  let g := hash[6]!
  let h := hash[7]!

  let t1 := h + (ShaU32.sum_1 (U32:=U32) (U8:=U8) e) +
                (ShaU32.ch (U32:=U32) (U8:=U8) e f g) + round_constants_224_256[i]! +
            ws[i]!
  let t2 := (ShaU32.sum_0 (U32:=U32) (U8:=U8) a) +
            (ShaU32.maj (U32:=U32) (U8:=U8) a b c)

  let h := g
  let g := f
  let f := e
  let e := d + t1
  let d := c
  let c := b
  let b := a
  let a := t1 + t2

  #[a, b, c, d, e, f, g, h]

def shuffle (ws:RoundConstantsTable U32) (hash: Hash U32) : Hash U32 :=
  aux hash 0
where
  aux a (i:Nat) :=
    if i>=64 then a else
    let hash := shuffle_i (U32:=U32) (U8:=U8) ws a i
    aux hash (i+1)

def compress (block : Block U32) (hash : Hash U32) : Hash U32 :=
  let ws := schedule (U32:=U32) (U8:=U8) block
  let hash' := shuffle (U32:=U32) (U8:=U8) ws hash
  -- Section 6.2.2 step 4
  Array.zipWith (· + ·) hash' hash

-- TODO this should return Sha256digest
def digest (msg : Array U8) : Hash U32 :=
  let blocks := padding msg
  let blocks := parse_blocks blocks
  process_blocks blocks initial_hash 0
where
  process_blocks (blocks : Array (Block U32)) (acc : Hash U32) i :=
    if i >= blocks.size then acc else
    let acc := compress (U32:=U32) (U8:=U8) blocks[i]! acc
    process_blocks blocks acc (i+1)

end Clap.Sha2
