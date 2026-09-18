import Clap.Lang.Core.F.mkF
namespace Clap.Lang

variable {p : ℕ}

/-- A byte as a single field element. -/
def ofUInt8 (u : UInt8) : ClapM p (F p) :=
  mkF (u.toNat : ZMod p)

namespace ofUInt8

lemma convertsM
  {state : ClapMState p}
  {u : UInt8}
:
  ConvertsM F.conversion (ofUInt8 (p := p) u) state (u.toNat : ZMod p) True
:= by
  unfold ofUInt8
  exact mkF.convertsM

end Clap.Lang.ofUInt8
