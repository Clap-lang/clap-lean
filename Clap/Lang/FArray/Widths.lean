import Clap.Lang.FArray.assert_eq
import Clap.Lang.FArray.default
import Clap.Lang.FArray.ofBitVec
import Clap.Lang.FArray.zeroExtend

/-!
# Fixed-width bit vectors
-/

namespace Clap.Lang

variable {p : ℕ}

abbrev FBV8 (p : ℕ) := FArray p 8
abbrev F32 (p : ℕ) := FArray p 32
abbrev F64 (p : ℕ) := FArray p 64

namespace FBV8

def ofUInt8 (u : UInt8) : ClapM p (FBV8 p) :=
  FArray.ofBitVec u.toBitVec

namespace ofUInt8

lemma convertsM
  [p.AtLeastTwo]
  {u : UInt8}
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (ofUInt8 (p := p) u) state
    (Vector.ofFn (fun i ↦ u.toBitVec[i])) True
:= FArray.ofBitVec.convertsM

end ofUInt8

end FBV8


namespace F32

def default : ClapM p (F32 p) :=
  FArray.default 32

namespace default

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (default (p := p)) state (Vector.replicate 32 false) True
:= FArray.default.convertsM

end default

def ofUInt32 (u : UInt32) : ClapM p (F32 p) :=
  FArray.ofBitVec u.toBitVec

namespace ofUInt32

lemma convertsM
  [p.AtLeastTwo]
  {u : UInt32}
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (ofUInt32 (p := p) u) state
    (Vector.ofFn (fun i ↦ u.toBitVec[i])) True
:= FArray.ofBitVec.convertsM

end ofUInt32

/-- Zero-extend a byte to 32 bits. Old model: `F32.ofFBV8`. -/
def ofFBV8 (u8 : FBV8 p) : ClapM p (F32 p) :=
  FArray.zeroExtend u8 24

namespace ofFBV8

lemma convertsM
  [p.AtLeastTwo]
  {u8 : FBV8 p}
  {vals : Vector Bool 8}
  {state : ClapMState p}
  (h_u8 : Converts FArray.conversion state u8 vals)
:
  ConvertsM FArray.conversion (ofFBV8 u8) state
    (vals ++ Vector.replicate 24 false) True
:= FArray.zeroExtend.convertsM (w' := 24) h_u8

end ofFBV8

def assert_eq (a b : F32 p) : ClapM p Unit :=
  FArray.assert_eq a b

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {a b : F32 p}
  {a_vals b_vals : Vector Bool 32}
  {state : ClapMState p}
  (h_a : Converts FArray.conversion state a a_vals)
  (h_b : Converts FArray.conversion state b b_vals)
:
  ConvertsM FUnit.conversion (assert_eq a b) state ()
    (∀ i : Fin 32, a_vals[i] = b_vals[i])
:= FArray.assert_eq.convertsM h_a h_b

end assert_eq

end F32

end Clap.Lang
