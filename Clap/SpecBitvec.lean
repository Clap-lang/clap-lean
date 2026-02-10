import Clap.Primes
import Clap.Spec
import Clap.SpecUint

universe u v w x

section Wheels

-- @[inline]
-- def Vector.zipWithM {n} {m : Type u → Type v} [Monad m] {α : Type w} {β : Type x} {γ : Type u}
--   (f : α → β → m γ) (as : Vector α n) (bs : Vector β n) : m (Vector γ n) := do
--   go 0 (Nat.zero_le n) #v[]
-- where
--   go (k : Nat) (h : k ≤ n) (acc : Vector γ k) : m (Vector γ n) := do
--     if h' : k < n then
--       go (k + 1) (by omega) (acc.push (← f as[k] bs[k]))
--     else
--       return acc.cast (by omega)

end Wheels

open Clap Lang Core

variable (p : ℕ) [Fact (Nat.Prime p)] [Core p]

namespace FBitVec

def length (x : @FBitVec p _ _) : F p :=
  List.foldl (fun acc _ ↦ acc + 1) (0 : F p) x

def assertLength (w : F p) (x : @FBitVec p _ _) : Option Unit := do
  eq0 ((length p x) - w)

end FBitVec

namespace Bin

-- necessary?
def assertBit (a : F p) : Option Unit :=
  eq0 (a * (a - 1))

def and  (a b : FB p) : FB p := a * b
def or   (a b : FB p) : FB p := a + b - a * b
def not  (a : FB p)   : FB p := 1 + a - 2 * a
def nand (a b : FB p) : FB p := 1 - a * b
def xor  (a b : FB p) : FB p := a + b - 2 * a * b
def nor  (a b : FB p) : FB p := a * b + 1 - a - b

-- (sum, carry)
private def halfAdder (a b : FB p) : (FB p × FB p) :=
  (Bin.xor p a b, Bin.and p a b)

-- (sum, carry)
def fullAdder (a b c : FB p) : (FB p × FB p) :=
  let (sum1, carry1) := halfAdder p a b
  let (sum2, carry2) := halfAdder p sum1 c
  (sum2, carry1 + carry2)

#eval fullAdder (p := Primes.babybear) 0 0 0 -- (0,0)
#eval fullAdder (p := Primes.babybear) 1 0 0 -- (1,0)
#eval fullAdder (p := Primes.babybear) 0 1 0 -- (1,0)
#eval fullAdder (p := Primes.babybear) 0 0 1 -- (1,0)
#eval fullAdder (p := Primes.babybear) 1 1 0 -- (0,1)
#eval fullAdder (p := Primes.babybear) 1 0 1 -- (0,1)
#eval fullAdder (p := Primes.babybear) 1 1 1 -- (1,1)

end Bin

abbrev FBitVec8 := List (FB p)

namespace FBitvec8

@[inline]
def assertBV8 : FBitVec8 p → Option Unit := FBitVec.assertLength p 8

@[inline]
def zero : FBitVec8 p := List.replicate 8 (0 : FB p)

def eq (a b : FBitVec8 p) : Option (FB p) := do
  assertBV8 p a -- necessary?
  assertBV8 p b

  let eql : FBitVec8 p ←
    a.zipWithM (fun a b ↦ do let eqv : FB p ← FB.eq a b; eqv) b
  eql.foldl (fun acc (x : FB p) ↦ do FB.and (← acc) x) (1 : FB p)

def toF (v : FBitVec8 p) : F p :=
  aux (1 : ZMod p) (const 0) v
where
  aux pow acc v :=
    match v with
    | [] => acc
    | b::rest =>
        let acc := acc + ((convert b) * (const pow))
        aux (pow * 2) acc rest

end FBitvec8

-- LSB
abbrev FBitVec32 := List (FB p)

namespace FBitVec32

@[inline]
def assertBV32 : FBitVec32 p → Option Unit := FBitVec.assertLength p 32

@[inline]
def zero : FBitVec32 p := List.replicate 32 (0 : FB p)

def add (a b : FBitVec32 p) : Option (FBitVec32 p) := do
  assertBV32 p a
  assertBV32 p b
  let r ← aux a b 0
  assertBV32 p r -- necessary?
  return r
where
  aux (a b : FBitVec) (c : FB p) : FBitVec :=
    match a, b with
    | [], [] => []
    | x :: xs, y :: ys =>
      let (sum, carry) := Bin.fullAdder p x y c
      sum :: aux xs ys carry
    | _, _ => []

end FBitVec32
