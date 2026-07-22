import Clap.Lang.F.F
import Clap.eDSLState.Spec

namespace Clap.Edsl.Lang

abbrev F8 p := F p

namespace F8

variable {p : ℕ}

/--
Taken form Clap.Edsl.Lang.FArray.oneHotRaw, which doesn't compile at the moment
-/
def isValidRange (varStore : VarStore p) (x : F p) (lt : ℕ) : Prop :=
  (x.eval varStore).any (λ val => val.val < lt)

def ofUInt8  (u : UInt8) : F8 p := UInt8.toFin u

def toUInt8 (f : F8 p) (varStore : VarStore p) : UInt8 :=
  f.eval varStore |>.getD 0 |>.val |> UInt8.ofNat

def ofChar (c : Char) : F8 p := ofUInt8 c.toUInt8

def toChar (c : F8 p) (varStore : VarStore p) : Char :=
  Char.ofUInt8 (F8.toUInt8 c varStore)

def isValid (x : F8 p) (varStore : VarStore p) : Prop :=
  isValidRange varStore x (2^8)

end F8

namespace Spec.F8

variable {p : ℕ}

private lemma ofUInt8_toUInt8 [NeZero p] (u : UInt8) (hp : 2^8 < p)
  (varStore : VarStore p) :
  F8.toUInt8 (F8.ofUInt8 u) varStore = u
:= by
  unfold F8.ofUInt8 F8.toUInt8
  show UInt8.ofNat ((((UInt8.toFin u).val : ℕ) : ZMod p).val) = u
  rw [ZMod.val_natCast]
  have h_toFin : (UInt8.toFin u).val = u.toNat := rfl
  have hu : u.toNat < 256 := u.toNat_lt
  have h_lt_p : (UInt8.toFin u).val < p := by rw [h_toFin]; omega
  rw [Nat.mod_eq_of_lt h_lt_p]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', h_toFin]
  exact Nat.mod_eq_of_lt hu

private lemma Char.toUInt8_ofUInt8 (n : UInt8) :
  Char.toUInt8 (Char.ofUInt8 n) = n
:= by
  show (Char.ofUInt8 n).val.toUInt8 = n
  show n.toUInt32.toUInt8 = n
  exact UInt8.toUInt8_toUInt32 n

private lemma Char.ofUInt8_toUInt8 {c : Char} (hc : c.toNat < 256) :
  Char.ofUInt8 (Char.toUInt8 c) = c
:= by
  apply Char.ext
  apply UInt32.toNat.inj
  show (Char.toUInt8 c).toUInt32.toNat = c.val.toNat
  rw [UInt8.toNat_toUInt32]
  show (c.val).toUInt8.toNat = c.val.toNat
  rw [UInt32.toNat_toUInt8]
  exact Nat.mod_eq_of_lt hc

private lemma ofChar_toChar [NeZero p] {x : F8 p} (varStore : VarStore p)
  (h : x.isValid varStore) :
  (F8.ofChar (F8.toChar x varStore)).eval varStore = x.eval varStore
:= by
  unfold F8.ofChar F8.toChar
  rw [Char.toUInt8_ofUInt8]
  unfold F8.toUInt8
  rcases hf : [varStore|x] with (_ | x')
  · simp [F8.isValid, F8.isValidRange] at h
    rw [hf] at h
    contradiction
  · simp_all [F8.isValid, F8.isValidRange]
    unfold F8.ofUInt8
    simp [Nat.mod_eq_of_lt h]

private lemma toChar_ofChar [NeZero p] {c : Char} (varStore : VarStore p)
  (hc : c.toNat < 256)
  (hp : 2^8 < p) :
  F8.toChar (F8.ofChar (p:=p) c) varStore = c
:= by
  unfold F8.ofChar F8.toChar
  rw [ofUInt8_toUInt8 _ hp]
  exact Char.ofUInt8_toUInt8 hc

end Spec.F8
