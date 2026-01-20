import Clap.Primes
import Clap.Spec

namespace Clap.Spec

variable {p : ℕ} [Fact (Nat.Prime p)]

abbrev FB p := ZMod p

namespace FB

def isValid (x:FB p) : Prop := x.val < 2

def Valid : Type := {x:FB p // x.isValid }

instance : CoeOut (FB p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FB p) where
  coe x := x.val

-- instance : CoeOut (@Valid p) ℕ where
--   coe x := x.val

def true (h:p≠1): @Valid p := ⟨1, by simp [isValid]; rw [ZMod.val_one''] ; simp ; assumption⟩
def false : @Valid p := ⟨0, by simp [isValid]⟩

end FB


abbrev FU8 p := ZMod p

namespace FU8

def isValid (x:FU8 p) : Prop := x.val < 2^8

def Valid : Type := {x:FU8 p // x.isValid }

instance : CoeOut (FU8 p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FU8 p) where
  coe x := x.val

-- instance : CoeOut (@Valid p) ℕ where
--   coe x := x.val

def mk (x:FU8 p) : Option Unit := Spec.assert_range 8 x

def mk_some (x:FU8 p) (h:x.val<256) : x.mk = some () := by
  aesop (add simp [mk,Spec.assert_range,Spec.num2bits])

def add (a b : FU8 p) : Option (FU8 p) := do
  let o := a + b
  Spec.assert_range 8 o
  o

-- instance : Coe Nat (FU8 p) where
--   coe n := n

instance : Coe UInt8 (FU8 p) where
  coe n := n.toNat

-- instance {n:Nat} : OfNat (FU8 p) n where
--   ofNat := n

-- instance : Coe Nat (FU8 p) where
--   coe n := n

end FU8


abbrev FU32 p := ZMod p

namespace FU32

def isValid (x:FU32 p) : Prop := x.val < 2^32

def Valid : Type := {x:FU32 p // x.isValid }

instance : CoeOut (FU32 p) ℕ where
  coe x := x.val

instance : CoeOut (@Valid p) (FU32 p) where
  coe x := x.val

-- instance : CoeOut (@Valid p) ℕ where
--   coe x := x.val

def mk (x:FU32 p) : Option Unit := Spec.assert_range 32 x

def mk_some (x:FU32 p) (h:x.val<2^32) : x.mk = some () := by
  aesop (add simp [mk,Spec.assert_range,Spec.num2bits])

-- instance : Coe (FU8 p) (FU32 p) where
--   coe u8 := u8

def addOption (a b : FU32 p) : Option (FU32 p) := do
  let o := a + b
  Spec.assert_range 8 o
  o

instance : HAnd (FU32 p) (FU32 p) (FU32 p) where
  hAnd := (· + ·)

end FU32


namespace ByteArray

def of_nat_be (x:ℕ) (len:Nat) : Array (FU8 p) :=
    (List.reverse (aux x len)).toArray
  where
    aux (x:ℕ) (len:Nat) : List (FU8 p) :=
      let d : ℕ := x / (2^8)
      let r : ℕ := x % (2^8)
      -- let r : UInt8 := UInt8.ofNatLT r.val (by sorry)
      let r : FU8 p := r -- does not wrap as r < 256
      if len=0 then [] else
      r::(aux d (len-1))

#guard
  let n : ℕ := 255 + 1
  of_nat_be (p:=Primes.babybear) n 2 = #[1,0]
#guard
  let n : ℕ := 2^16 + 2
  of_nat_be (p:=Primes.babybear) n 3 = #[1,0,2]
#guard
  let n : ℕ := 2^16 + 2
  of_nat_be (p:=Primes.babybear) n 4 = #[0,1,0,2]

/-
Rust playground
let z : u32 = 65536 + 2;
dbg!(z.to_be_bytes());  # [0,1,0,2]
-/

def to_nat_be (bs:Array (FU8 p)) : ℕ :=
  Array.foldl (fun acc (b:ZMod p) => acc * 256 + (b:ℕ)) (0:ℕ) bs

#guard to_nat_be (p:=Primes.babybear) #[1] = 1
#guard to_nat_be (p:=Primes.babybear) #[255,1] = 255*256+1

def min_bits (x:ℕ) : ℕ :=
  let n_bits := Nat.log2 x
  if 2^n_bits < x then n_bits+1 else n_bits

def min_bytes (x:ℕ) : ℕ :=
  let n_bits := min_bits x
  if n_bits % 8 = 0 then n_bits / 8 else (n_bits / 8) + 1

lemma roundrip1 (x:ℕ) (len:ℕ) (h: len <= min_bytes x) :
  to_nat_be (of_nat_be (p:=p) x len) = x := sorry

#guard
  let n : ℕ := 255 + 1
  to_nat_be (of_nat_be (p:=Primes.babybear) n 2) = n
#guard
  let n : ℕ := 2^16 + 2
  to_nat_be (of_nat_be (p:=Primes.babybear) n 3) = n
#guard
  let n : ℕ := 2^16 + 2
  to_nat_be (of_nat_be (p:=Primes.babybear) n 4) = n

lemma roundrip2 (bs:Array (FU8 p)) :
  of_nat_be (to_nat_be bs) bs.size = bs := sorry

#guard of_nat_be (p:=Primes.babybear) (to_nat_be (p:=Primes.babybear) #[1]) 1 = #[1]
#guard of_nat_be (p:=Primes.babybear) (to_nat_be  (p:=Primes.babybear) #[255,1]) 2 = #[255,1]

end ByteArray

#check BitVec

abbrev FBitVec p := List (ZMod p)

namespace BitVec

-- def decompose {h:2^32<p} (e:FU32 p) : FBitVec 32 p :=
--   Spec.assert_range e 32

end BitVec

end Clap.Spec
