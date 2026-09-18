import Clap.Lang.Core.F.mkF
namespace Clap.Lang.FArray

variable {p : ℕ}

/-- An all-zero bit vector. -/
def default (w : ℕ) : ClapM p (FArray p w) := do
  let zeroRef ← mkF 0
  return Vector.replicate w zeroRef

namespace default

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (default (p := p) w) state (Vector.replicate w false) True
:= by
  unfold default
  step mkF.convertsM as zeroRef
  apply convertsM_pure
  . exact FArray.converts_replicate (FB.converts_zero h_zeroRef)
  . trivial

end Clap.Lang.FArray.default
