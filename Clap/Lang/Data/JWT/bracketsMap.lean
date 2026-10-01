import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.Combinators.mapM
namespace Clap.Lang

variable {p : ℕ}

def bracketsMap [p.AtLeastTwo] {w} (input : FVec p w) : ClapM p (FVec p w) := do
  input.mapM (fun c ↦ do
    let eqOpen ← eq c (← mkF '{'.toNat)
    let eqClose ← eq c (← mkF '}'.toNat)
    eqOpen - eqClose
    )

namespace bracketsMap

/-- Per-element step: `c ↦ (c == '{') - (c == '}')`, i.e. `1` on an open brace, `-1` on a close
brace, `0` otherwise. Needs `'{'` and `'}'` to remain distinct field elements, hence `h_p`. -/
private lemma step_convertsM
  [p.AtLeastTwo]
  (h_p : 2 ^ (8 + 1) < p)
  {state : ClapMState p}
  {x : F p}
  {x_val : ZMod p}
  (h_x : Converts F.conversion state x x_val)
:
  ConvertsM F.conversion
    (do
      let eqOpen ← eq x (← mkF '{'.toNat)
      let eqClose ← eq x (← mkF '}'.toNat)
      eqOpen - eqClose)
    state
    (if x_val == ('{'.toNat : ZMod p) then 1 else if x_val == ('}'.toNat : ZMod p) then -1 else 0)
    True
:= by
  have hp512 : 512 < p := by simpa using h_p
  step mkF.convertsM as openB
  step eq.convertsM h_x h_openB as eqOpen
  step mkF.convertsM as closeB
  step eq.convertsM h_x h_closeB as eqClose
  have h_eqOpen_f := F.converts_of_FB_converts h_eqOpen
  have h_eqClose_f := F.converts_of_FB_converts h_eqClose
  apply convertsM_of_convertsM (mkSub.convertsM h_eqOpen_f h_eqClose_f)
  · have e123 : ('{'.toNat : ZMod p) = 123 := by norm_cast
    have e125 : ('}'.toNat : ZMod p) = 125 := by norm_cast
    have hne : (123 : ZMod p) ≠ 125 := by
      have h123 : ((123 : ℕ) : ZMod p) = 123 := by norm_cast
      have h125 : ((125 : ℕ) : ZMod p) = 125 := by norm_cast
      rw [← h123, ← h125]
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (show (123:ℕ) < p by omega),
          ZMod.val_natCast_of_lt (show (125:ℕ) < p by omega)] at hv
      omega
    rw [e123, e125]
    by_cases h1 : x_val = (123 : ZMod p)
    · simp [h1, hne]
    · by_cases h2 : x_val = (125 : ZMod p)
      · simp [h2, hne.symm]
      · simp [h1, h2]
  · trivial

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a : FVec p k}
  {a_val : Vector (ZMod p) k}
  (h_a : Converts FVec.conversion state a a_val)
  (h_p : 2 ^ (8 + 1) < p)
:
  ConvertsM FVec.conversion (bracketsMap a) state
    (a_val.map fun c : ZMod p ↦
      if c == '{'.toNat then 1 else if c == '}'.toNat then -1 else 0
    )
    True
:= convertsM_mapM (FVec.converts_iff_F_converts.mp h_a) (step_convertsM h_p)

end bracketsMap

end Clap.Lang
