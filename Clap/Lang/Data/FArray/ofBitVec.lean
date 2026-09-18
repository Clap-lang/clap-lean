import Clap.Lang.Core.F.mkF
namespace Clap.Lang.FArray

variable {p : ℕ}

/--
A constant bit vector, LSB first.
-/
def ofBitVec {w : ℕ} (bv : BitVec w) : ClapM p (FArray p w) := do
  let zeroRef ← mkF 0
  let oneRef ← mkF 1
  return Vector.ofFn (fun i ↦ if bv[i] then oneRef else zeroRef)

namespace ofBitVec

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {bv : BitVec w}
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (ofBitVec (p := p) bv) state (Vector.ofFn (fun i ↦ bv[i])) True
:= by
  unfold ofBitVec
  step mkF.convertsM as zeroRef
  step mkF.convertsM as oneRef
  apply convertsM_pure
  . apply FArray.converts_ofFn
    intro i
    by_cases h : bv[i]
    . simpa [h] using FB.converts_one h_oneRef
    . simpa [h] using FB.converts_zero h_zeroRef
  . trivial

end Clap.Lang.FArray.ofBitVec
