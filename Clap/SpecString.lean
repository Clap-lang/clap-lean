import Clap.SpecUint

namespace Clap
open Clap.Spec

variable {p : ℕ} [Fact (Nat.Prime p)] {maxLen : ℕ}

variable {F : Type}
  [HAdd F F F]
  [HSub F F F]
  [ToString F] -- TODO remove?

variable {FB : Type}
  [Zero FB] -- false
  [One FB]  -- true
  [Coe FB F]
  [Inhabited FB]
  [HAdd FB FB FB] -- Or
  [HMul FB FB FB] -- And
  [HSub FB FB FB] -- Xor
  [ToString FB] -- TODO remove?

variable {F8 : Type}
  [Coe F8 F]
  [Inhabited F8]

variable [@Core F FB]
open Core

structure MyString (p maxLen:ℕ) where
  chars : Vector F8 maxLen
  len : F8

def assertString (s : MyString (F8:=F8) p maxLen) : Option Unit := do
  for i in [0:maxLen] do
    let b <- Spec.F.eq (s.chars[i]!:F) (const 0)
    -- not(i<len) <-> len<=i
    let expected <- Spec.F.lessThanEq maxLen (s.len:F) (const i)
    Spec.FB.assert_eq (F:=F) b expected

open Primes

def ok : MyString (p:=babybear) (F8:=ZMod babybear) (maxLen:=3) := {
  chars := #v[0x11,0x15,0x00]
  len := 2
}

def ko : MyString (p:=babybear) (F8:=ZMod babybear) (maxLen:=3) := {
  chars := #v[0x11,0x15,0x00]
  len := 3
}

#guard (assertString (F:=ZMod babybear) ok) = some ()
#guard (assertString (F:=ZMod babybear) ko) = none

end Clap
