import Clap.Primes
import Clap.Poseidon.ConstantC
import Clap.Poseidon.ConstantM
import Clap.Poseidon.ConstantP
import Clap.Poseidon.ConstantS
import Clap.Lang.F.F

namespace Clap.Poseidon.Constant

open Primes C M P S

set_option maxRecDepth 10000

@[aesop simp]
def Cl (t:ℕ) := match t with
  |  2 => 72
  |  3 => 81
  |  4 => 88
  |  5 => 100
  |  6 => 108
  |  7 => 119
  |  8 => 128
  |  9 => 135
  | 10 => 140
  | 11 => 154
  | 12 => 156
  | 13 => 169
  | 14 => 182
  | 15 => 180
  | 16 => 192
  | 17 => 204
  | _ => 0

def C (i:ℕ) : Vector (ZMod bn254) (Cl i) :=
  if h: i=2  then ⟨C02.toArray, by aesop⟩ else
  if h: i=3  then ⟨C03.toArray, by aesop⟩ else
  if h: i=4  then ⟨C04.toArray, by aesop⟩ else
  if h: i=5  then ⟨C05.toArray, by aesop⟩ else
  if h: i=6  then ⟨C06.toArray, by aesop⟩ else
  if h: i=7  then ⟨C07.toArray, by aesop⟩ else
  if h: i=8  then ⟨C08.toArray, by aesop⟩ else
  if h: i=9  then ⟨C09.toArray, by aesop⟩ else
  if h: i=10 then ⟨C10.toArray, by aesop⟩ else
  if h: i=11 then ⟨C11.toArray, by aesop⟩ else
  if h: i=12 then ⟨C12.toArray, by aesop⟩ else
  if h: i=13 then ⟨C13.toArray, by aesop⟩ else
  if h: i=14 then ⟨C14.toArray, by aesop⟩ else
  if h: i=15 then ⟨C15.toArray, by aesop⟩ else
  if h: i=16 then ⟨C16.toArray, by aesop⟩ else
  if h: i=17 then ⟨C17.toArray, by aesop⟩ else
  Vector.mk (n:=Cl i) #[] (by aesop)

def Ms (i:ℕ) := if i < 18 then i else 0

def Vector.squareMatrix (k:ℕ) : Vector (Vector (ZMod bn254) k) k :=
  Vector.replicate k (Vector.replicate k 0)

def M (i:ℕ) : Vector (Vector (ZMod bn254) i) i :=
  match h : i with
  |  2 => M02
  |  3 => M03
  |  4 => M04
  |  5 => M05
  |  6 => M06
  |  7 => M07
  |  8 => M08
  |  9 => M09
  | 10 => M10
  | 11 => M11
  | 12 => M12
  | 13 => M13
  | 14 => M14
  | 15 => M15
  | 16 => M16
  | 17 => M17
  | _ => h ▸ Vector.squareMatrix i

def P (i:ℕ) : Vector (Vector (ZMod bn254) i) i :=
  match h : i with
  |  2 => P02
  |  3 => P03
  |  4 => P04
  |  5 => P05
  |  6 => P06
  |  7 => P07
  |  8 => P08
  |  9 => P09
  | 10 => P10
  | 11 => P11
  | 12 => P12
  | 13 => P13
  | 14 => P14
  | 15 => P15
  | 16 => P16
  | 17 => P17
  | _ => h ▸ Vector.squareMatrix i

@[aesop simp]
def Sl (t:ℕ) := match t with
  |  2 => 168
  |  3 => 285
  |  4 => 392
  |  5 => 540
  |  6 => 660
  |  7 => 819
  |  8 => 960
  |  9 => 1071
  | 10 => 1140
  | 11 => 1386
  | 12 => 1380
  | 13 => 1625
  | 14 => 1890
  | 15 => 1740
  | 16 => 1984
  | 17 => 2244
  | _ => 0

def S (i:ℕ) : Vector (ZMod bn254) (Sl i) :=
  if h2:  i=2  then ⟨S02.toArray, by aesop⟩ else
  if h3:  i=3  then ⟨S03.toArray, by aesop⟩ else
  if h4:  i=4  then ⟨S04.toArray, by aesop⟩ else
  if h5:  i=5  then ⟨S05.toArray, by aesop⟩ else
  if h6:  i=6  then ⟨S06.toArray, by aesop⟩ else
  if h7:  i=7  then ⟨S07.toArray, by aesop⟩ else
  if h8:  i=8  then ⟨S08.toArray, by aesop⟩ else
  if h9:  i=9  then ⟨S09.toArray, by aesop⟩ else
  if h10: i=10 then ⟨S10.toArray, by aesop⟩ else
  if h11: i=11 then ⟨S11.toArray, by aesop⟩ else
  if h12: i=12 then ⟨S12.toArray, by aesop⟩ else
  if h13: i=13 then ⟨S13.toArray, by aesop⟩ else
  if h14: i=14 then ⟨S14.toArray, by aesop⟩ else
  if h15: i=15 then ⟨S15.toArray, by aesop⟩ else
  if h16: i=16 then ⟨S16.toArray, by aesop⟩ else
  if h17: i=17 then ⟨S17.toArray, by aesop⟩ else
  Vector.mk (n:=Sl i) #[] (by aesop)

end Clap.Poseidon.Constant
