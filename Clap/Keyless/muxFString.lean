import Clap.Keyless.Input
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.Combinators.mapM

open Clap Lang FString Primes

/-- Multiplexer for FString: `if sel then a else b`. CIRCOM: `out[i] = (a[i] - b[i]) * sel + b[i]` -/
def muxFString {maxLen : ℕ} (sel : FB bn254) (a b : FString bn254 maxLen) :
  ClapM bn254 (FString bn254 maxLen)
:= do
  pure
    { data := ← (a.data.zip b.data).mapM (fun xy ↦ conditionalSwap sel xy.1 xy.2)
      len := ← conditionalSwap sel a.len b.len
    }

namespace muxFString

lemma convertsM {state : ClapMState bn254} {maxLen : ℕ}
  {sel : FB bn254}
  {a b : FString bn254 maxLen}
  -- Ideal values
  {sel_val : Bool}
  {a_val b_val : String}
  -- Conversion hypotheses
  (h_sel : Converts FB.conversion state sel sel_val)
  (h_a : Converts FString.conversion state a a_val)
  (h_nb : Converts FString.conversion state b b_val)
  :
  ConvertsM FString.conversion (muxFString sel a b) state
    (if sel_val then a_val else b_val)
    True
:= by
  unfold muxFString
  have h_a_data := FString.converts_data h_a
  have h_b_data := FString.converts_data h_nb
  step (convertsM_mapM_ctx
    (f := fun (s : FB bn254) (xy : F bn254 × F bn254) ↦ conditionalSwap s xy.1 xy.2)
    (f_spec := fun (s : Bool) (xy : ZMod bn254 × ZMod bn254) ↦ if s then xy.1 else xy.2)
    h_sel (fun i ↦ FVec.converts_zip h_a_data h_b_data i.isLt)
    (fun h_ctx h_x ↦ conditionalSwap.convertsM h_ctx (FPair.converts_fst h_x) (FPair.converts_snd h_x)))
    as data
  step conditionalSwap.convertsM h_sel (FString.converts_len h_a) (FString.converts_len h_nb) as len
  apply convertsM_pure
  . apply FString.converts_intro
    . refine converts_of_converts h_data ?_
      cases sel_val <;> (ext i hi; simp [Vector.getElem_map, Vector.getElem_zip])
    . refine converts_of_converts h_len ?_
      cases sel_val <;> simp
  . trivial

end muxFString
