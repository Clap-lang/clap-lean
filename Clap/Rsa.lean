--import Mathlib.Data.ZMod.Defs

-- https://datatracker.ietf.org/doc/html/rfc8017

-- TODO result monad

def BIT_SIZE: UInt32  := 2048
def BYTE_SIZE: UInt32 := BIT_SIZE / 8
def HLEN: Nat := 32 -- sha256 / 8 = 32 -- TODO this was usize

-- abbrev RSAInt : Type := BitVec 2048 -- UInt is a BitVec
abbrev RSAInt : Type := Fin (2^2048) -- BitVec is a Fin
--abbrev RSAInt : Type := ZMod 2048

instance : Coe UInt8 RSAInt where
  coe (u8:UInt8) :=
    Fin.mk u8.toFin (by sorry )

namespace RSAInt
  def pow_mod (base exp mod:RSAInt) : RSAInt := sorry

  def from_byte_seq_be (bs:ByteArray) : RSAInt :=
    bs.foldl (fun acc b => acc * 256 + b) 0

  def to_byte_seq_be (x:RSAInt) (len:Nat) : ByteArray :=
    ByteArray.mk (List.reverse (aux x len)).toArray
  where
    aux (x:RSAInt) (len:Nat) : List UInt8 :=
      let a := x / (2^8)
      let r : RSAInt := x % (2^8)
      -- let r : UInt8 := UInt8.ofNatLT r.val (by sorry)
      let r : UInt8 := UInt8.ofNat r.val
      if len=0 then [] else
      r::(aux a (len-1))

#eval to_byte_seq_be (65536 + 2) 4

/-
Rust playground
let z : u32 = 65536 + 2;
dbg!(z.to_be_bytes());  # [0,1,0,2]
-/

end RSAInt

def oassert (b:Bool) : Option Unit := if b then some () else none
def ofail (b:Bool) : Option Unit := if b then none else some ()

def SK : Type := RSAInt × RSAInt
-- TODO these two are supposed to be positive integers
-- e for us is fixed to 65537
def PK : Type := RSAInt × RSAInt
  -- n : Nat -- the RSA modulus
  -- e : Nat -- the RSA public exponent

-- abbrev SIG := Nat -- signature representative, an integer between 0 and n - 1
-- abbrev MSG := Nat -- message   representative, an integer between 0 and n - 1

-- TODO this assumes pk is valid
def RSAVP1 (pk:PK) (s:RSAInt) : Option RSAInt := do
  let (n,e) := pk
  ofail (s > n - 1)
  (s.pow_mod e n) -- s^e % n

/-
 OS2IP converts an octet string to a nonnegative integer.
 TODO if the bytes are all zero the Nat is going to be zero, not sure how to enforce the non-negative result
-/
def OS2IP (bs:ByteArray) : RSAInt := RSAInt.from_byte_seq_be bs

-- TODO x non negative, result of length xLen
def I2OSP : (x:RSAInt) -> (xLen:Nat) -> Option ByteArray := sorry
def EMSA_PKCS1_V1_5_ENCODE : (m:ByteArray) -> (mlen:Nat) -> Option ByteArray := sorry

-- this is used in EMSA_PKCS1_V1_5_ENCODE at some point
def SHA256_T := ByteArray.mk #[0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20]

def RSASSA_PKCS1_V1_5_VERIFY (pk:PK) (msg:ByteArray) (sig:ByteArray) : Option Unit :=
  -- TODO just for testing
  let k : Nat := 5 -- the length in octets of the RSA modulus n
  if sig.size != k then none
  else do
    let s : RSAInt := OS2IP sig
    let m <- RSAVP1 pk s
    let em <- I2OSP m k
    let em' <- EMSA_PKCS1_V1_5_ENCODE msg msg.size
    if em' = em then some () else none


/-
we should pass the same tests as keyless-zk-proofs/circuit/src/rsa.rs
note: they are always testing with messages of zeros

cargo test -- rsa::rsa_verify_should_pass_with_valid_input --nocapture

```
         let msg_len: usize = rng.gen_range(0, 9999);
-        let message: Vec<u8> = vec![0; msg_len];
+        let message: Vec<u8> = (0..msg_len).map(|_| rand::random::<u8>()).collect();

-        info!("Message generated, msg_hex={}", hex::encode(&message));
+        dbg!("Message generated, msg_hex={}", hex::encode(&message));
```

also they are only running the witgen and not checking the cs

optionally we should also test with https://github.com/hacspec/hacspec/blob/master/examples/rsa-pkcs1/src/rsa-pkcs1.rs

-/

/-

OpenID Connect (OIDC) uses RSA-based signing algorithms, primarily RS256, to secure ID tokens and other JWTs.

https://datatracker.ietf.org/doc/html/rfc7515#appendix-A.2

https://pkg.go.dev/crypto/rsa#VerifyPKCS1v15
-/
