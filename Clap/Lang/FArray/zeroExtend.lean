import Clap.Lang.F.mkF

namespace Clap.Lang.FArray

variable {p : ℕ}

/-- Pad a bit vector with `w'` high zero bits. Old model: the `++ Vector.replicate 24 0` in
`F32.ofFBV8`, generalised. -/
def zeroExtend {w : ℕ} (v : FArray p w) (w' : ℕ) : ClapM p (FArray p (w + w')) := do
  let zeroRef ← mkF 0
  return v ++ Vector.replicate w' zeroRef

namespace zeroExtend

lemma convertsM
  [p.AtLeastTwo]
  {w w' : ℕ}
  {v : FArray p w}
  {vals : Vector Bool w}
  {state : ClapMState p}
  (h_v : Converts FArray.conversion state v vals)
:
  ConvertsM FArray.conversion (zeroExtend v w') state
    (vals ++ Vector.replicate w' false) True
:= by
  unfold zeroExtend
  step mkF.convertsM as zeroRef
  apply convertsM_pure
  . exact FArray.converts_append h_v
      (FArray.converts_replicate (FB.converts_zero h_zeroRef))
  . trivial

end Clap.Lang.FArray.zeroExtend
