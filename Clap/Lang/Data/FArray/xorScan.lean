import Clap.Lang.Core.FB.xor
import Clap.Lang.Core.FB.ofBool
import Clap.Model.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

section xorScan

/-- Builds the inclusive prefix-xor scan of the first `j` elements of `vals`, one element at a
time, by pushing a new accumulator (`rest[j-1] xor vals[j-1]`) onto the previous scan. Index 0 of
the result is always `init`; index `i+1` is `init ^^ vals[0] ^^ ... ^^ vals[i]`. -/
def scanAux {k} (vals : FArray p k) (init : FB p) (j : ℕ) (hj : j ≤ k) :
    ClapM p (Vector (FB p) (j + 1)) :=
  match j, hj with
  | 0, _ => pure #v[init]
  | j + 1, hj => do
      let rest ← scanAux vals init j (by omega)
      let acc ← FB.xor rest[j] vals[j]
      return rest.push acc

/-- Pure mirror of `scanAux`, used as the `convertsM` ideal value. -/
def scanAuxPure {k} (vals_val : Vector Bool k) (init_val : Bool) (j : ℕ) (hj : j ≤ k) :
    Vector Bool (j + 1) :=
  match j, hj with
  | 0, _ => #v[init_val]
  | j + 1, hj =>
    let rest := scanAuxPure vals_val init_val j (by omega)
    rest.push (rest[j] ^^ vals_val[j])

namespace scanAux

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {vals : FArray p k}
  {vals_val : Vector Bool k}
  (h_vals : Converts FArray.conversion state vals vals_val)
  {init : FB p}
  {init_val : Bool}
  (h_init : Converts FB.conversion state init init_val)
  {j : ℕ}
  (hj : j ≤ k)
:
  ConvertsM FArray.conversion (scanAux vals init j hj) state
    (scanAuxPure vals_val init_val j hj) True
:= by
  induction j with
  | zero =>
    unfold scanAux scanAuxPure
    apply convertsM_pure
    . exact FArray.converts_push FArray.converts_empty h_init
    . trivial
  | succ j ih =>
    unfold scanAux scanAuxPure
    step @ih (by omega) as rest
    have h_rest_last := FArray.converts_getElem h_rest (show j < j + 1 by omega)
    have h_vals_j := FArray.converts_getElem h_vals (show j < k by omega)
    step FB.xor.convertsM h_rest_last h_vals_j as acc
    apply convertsM_pure
    . exact FArray.converts_push h_rest h_acc
    . trivial

end scanAux

/-- Inclusive prefix-xor scan of `vals`, starting the running xor from `false`, dropping the
leading (always-`false`-before-anything) element so the output has the same length as `vals`. -/
def FArray.xorScan {k} (vals : FArray p k) : ClapM p (FArray p k) := do
  let false' ← FB.ofBool false
  let full ← scanAux vals false' k (le_refl k)
  return full.tail

namespace FArray.xorScan

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {vals : FArray p k}
  {vals_val : Vector Bool k}
  (h_vals : Converts FArray.conversion state vals vals_val)
:
  ConvertsM FArray.conversion (vals.xorScan) state
    (Vector.cast (by omega) (scanAuxPure vals_val false k (le_refl k)).tail) True
:= by
  unfold FArray.xorScan
  step (FB.ofBool.convertsM (state := state) (b := false)) as false'
  step (scanAux.convertsM h_vals h_false' (le_refl k)) as full
  apply convertsM_pure
  . exact FArray.converts_vector_cast (FArray.converts_tail h_full) (by omega)
  . trivial

end FArray.xorScan

end xorScan

end Clap.Lang
