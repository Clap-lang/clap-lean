import Clap.Lang
import Clap.Compiler.Basic

namespace StringExample

open Clap.Lang

variable {p : ℕ} [abstractCore : Core p] [Fact (Primes.fits p 8)]

open Core

/--
info: abstractCore
-/
#guard_msgs in
#synth Core p

def g := 0
def l := 5
def r := 7

#eval (g*l) + (1-g)*r

open Clap.Lang.ZMod

-- ite : {α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α

-- conditional swap
def ite (guard: FB p) (then_: F p) (else_ : F p) : F p :=
  convert guard * then_ + (1 - convert guard) * else_

--def ite (c : Prop) [h : Decidable c] (t e : F p) : F p := t

abbrev pb := Primes.babybear

instance : Coe (Core.FB pb) Prop := ⟨(· = FB.true)⟩

example (b : FB pb): F pb := if b then const 1 else const 0

-- we need to define new syntax, there is no way to overload the exusting mechanism


-- #check decidable_of_iff

def countZeros {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (F p) := do
  Vector.foldlM (fun len f => do
    ite (F.eq f (const 0))
      (len + const 1)
      len
  ) (const 0) fs


-- def countZeros {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (F p) := do
--   Vector.foldlM (fun (len:F p) f => do
--     let b <- F.eq f (const 0)
--     some (len + convert b)
--   ) (const 0) fs

/--
  Zero-padded vector of bytes of length `len`.
  `len` can at most be `maxLen`.
-/
structure MyString (maxLen : ℕ) where
  chars : Vector (F8 p) maxLen
  len : F p

/--
  Takes an arbitrary vector of field elements and returns a MyString.
  Fails if the input contains an element that is not a byte.
-/
def MyString.ofVec {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (MyString (p:=p) maxLen) := do
  let zeros <- countZeros fs
  let len := maxLen - zeros
  let chars <- Vector.mapM F8.ofF! fs
  some {chars,len}

end StringExample

namespace TestStringExample

open Clap.Lang Core ZMod
open StringExample

abbrev p := Primes.babybear

def test {maxLen} (fs : Vector (F p) maxLen) : Option (F p) := do
  let s <- MyString.ofVec fs
  s.len

example : test #v[255,15,0] = some 2 := by native_decide
example : test #v[256,15,0] = none := by native_decide

end TestStringExample

namespace StringExampleCompile

open Clap.Lang Core
open StringExample

def test {p} [Core p] [Fact (Primes.fits p 8)](fs : (Vector (F p) 10)) : Option Unit := do
  let s <- MyString.ofVec fs
  eq0 s.len

open Clap.Lang.ZMod

#compile test using Primes.babybear

end StringExampleCompile
