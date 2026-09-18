import Clap.Lang.Core.F.ofUInt8
namespace Clap.Lang

variable {p : ℕ}

/-- A character as a single field element, via its low byte. -/
def ofChar (c : Char) : ClapM p (F p) :=
  ofUInt8 c.toUInt8

namespace ofChar

lemma convertsM
  {state : ClapMState p}
  {c : Char}
:
  ConvertsM F.conversion (ofChar (p := p) c) state (c.toUInt8.toNat : ZMod p) True
:= by
  unfold ofChar
  exact ofUInt8.convertsM

end Clap.Lang.ofChar
