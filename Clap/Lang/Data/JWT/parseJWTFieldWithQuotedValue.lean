import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.or
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Gate.isZero
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.arraySelectorComplex
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Core.FUnit.guardedAssertEq
import Clap.Lang.Data.JWT.parseJWTFieldSharedLogic
import Clap.Lang.Data.JWT.Basic
import Mathlib.Data.List.GetD
import Clap.Lang.Data.JWT.Scaffold.parseJWTFieldWithUnquotedValue
import Clap.Lang.Data.JWT.Scaffold.parseJWTFieldWithQuotedValue

namespace Clap.Lang

open Primes

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure QuotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field             : FString bn254 maxPairLen
  name              : FString bn254 maxNameLen
  value             : FString bn254 maxValueLen
  fieldStringBodies : PaddedVector (FB bn254) bn254 maxPairLen
  nameIndex         : F bn254
  colonIndex        : F bn254
  valueIndex        : F bn254

/-! ## Value-quote checks

`field[value_index - 1] = '"'` and `field[value_index + value_len] = '"'`, the quotes around the
value. Wrapped in its own `private def` purely to keep `parseJWTFieldWithQuotedValue`'s own
top-level `do` block short — see `parseJWTFieldSharedLogic.lean`'s identical rationale for
`checkNameClosingQuote`/`checkLastCharDelimiter`. -/

private def checkValueQuotes {maxKVPairLen : ℕ}
  (field_data : FVec bn254 maxKVPairLen)
  (perform : FB bn254)
  (valueIndex valueLen : F bn254) :
  ClapM bn254 Unit
:= do
  let one ← mkF 1
  let valueFirstQuote ← selectArrayValue maxKVPairLen field_data (← valueIndex - one)
  guardedAssertEq perform valueFirstQuote (← mkF 34)
  let valueSecondQuote ← selectArrayValue maxKVPairLen field_data (← valueIndex + valueLen)
  guardedAssertEq perform valueSecondQuote (← mkF 34)

/-- Whether a position falls in any of the three gaps between the name/colon, colon/value and
value/terminator — `nameColonGapDef`, `colonValueGapDef` and `valueEndGapDef` below, each wrapped
as its own opaque `where`-bound def (rather than inlined) so the combined proof in
`anyGapZone_convertsM` reasons about fixed function applications (trivially equal to themselves)
rather than inlined nested `do`-blocks (requiring expensive `whnf` unfolding to confirm two
mentions of "the state after gap X" agree) — the same wall `docs/proving-circuits.md` describes
for `Base64Len/base64UrlLookup.lean`. Each allocates its own `1`/`2` literal rather than taking one
as a parameter: hash-consing means a repeated `mkF` costs no new gate or witness allocation, so
there's no need to thread a shared constant through.

Unlike `parseJWTFieldWithUnquotedValue.lean`'s sibling, there *is* an opening/closing quote around
the value to skip past, so `colonValueGapDef` ends at `valueIndex - 1` (not `valueIndex`) and
`valueEndGapDef` starts at `valueIndex + valueLen + 1` (not `valueIndex + valueLen`) — matching
`parseEmailVerifiedField.lean`'s offsets rather than the unquoted sibling's.

`anyGapZoneDef` itself is wrapped as its own opaque def for a second, separate reason:
`checkWhitespaceZonesQuoted` calls this (rather than inlining the five steps) so that its own
`convertsM` proof can combine `anyGapZone_convertsM`'s fact with the `foldlM` part via a single
top-level bind, matching this symbol syntactically — never needing `bind_assoc` to re-associate a
right-nested `do`-block, which (confirmed experimentally) `simp` cannot do predictably at this
depth without producing a differently-shaped term that is no longer `hZones`-shaped. -/
private def anyGapZoneDef (maxKVPairLen : ℕ)
  (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) :
  ClapM bn254 (FArray bn254 maxKVPairLen)
:= do
  let zoneA ← nameColonGapDef maxKVPairLen nameLen colonIndex
  let zoneB ← colonValueGapDef maxKVPairLen colonIndex valueIndex
  let zoneC ← valueEndGapDef maxKVPairLen valueIndex valueLen fieldLen
  let inZoneAB ← zoneA.zipWithM FB.or zoneB
  inZoneAB.zipWithM FB.or zoneC
where
  /-- The gap strictly between the name's closing quote and the colon: positions
  `(nameLen + 2, colonIndex)`. -/
  nameColonGapDef (maxKVPairLen : ℕ) (nameLen colonIndex : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen)
  := do
    let two ← mkF 2
    let s ← mkAdd nameLen two
    arraySelectorComplex maxKVPairLen s colonIndex
  /-- The gap strictly between the colon and the opening value-quote: positions
  `(colonIndex + 1, valueIndex - 1)`. -/
  colonValueGapDef (maxKVPairLen : ℕ) (colonIndex valueIndex : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen)
  := do
    let one ← mkF 1
    let s ← mkAdd colonIndex one
    let e ← mkSub valueIndex one
    arraySelectorComplex maxKVPairLen s e
  /-- The gap strictly between the closing value-quote and the field's closing delimiter: positions
  `(valueIndex + valueLen + 1, fieldLen - 1)`. -/
  valueEndGapDef (maxKVPairLen : ℕ) (valueIndex valueLen fieldLen : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen)
  := do
    let one ← mkF 1
    let t ← mkAdd valueLen one
    let s ← mkAdd valueIndex t
    let e ← mkSub fieldLen one
    arraySelectorComplex maxKVPairLen s e

/-! ## Whitespace check over the quoted zones -/

private def checkWhitespaceZonesQuoted {maxKVPairLen : ℕ}
  (field_data : FVec bn254 maxKVPairLen)
  (perform : FB bn254)
  (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) :
  ClapM bn254 Unit
:= do
  let inZone ← anyGapZoneDef maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen
  (inZone.zip field_data).foldlM (b := ()) fun _ (z, c) ↦ do
    let ws ← F8.isWhitespace c
    guardedEq0 perform (← z.and (← not ws))

/-! ## Name/value selector agreement with `fieldStringBodies`

No direct analogue in the unquoted sibling. `nameSel`/`valueSel` (via `arraySelector`, not
`arraySelectorComplex`) mark the name/value content positions; `fieldStringBodies` must agree with
their union exactly (an `↔`), expressed as two guarded `and`-of-negation checks per position. -/

private def checkStringBodies {maxKVPairLen : ℕ}
  (perform : FB bn254)
  (nameLen valueIndex valueLen : F bn254)
  (sb_data : FArray bn254 maxKVPairLen) :
  ClapM bn254 Unit
:= do
  let one ← mkF 1
  let nameSel ← arraySelector maxKVPairLen one (← nameLen + one)
  let valueSel ← arraySelector maxKVPairLen valueIndex (← valueIndex + valueLen)
  let nameOrValue ← nameSel.zipWithM FB.or valueSel
  (nameOrValue.zip sb_data).foldlM (b := ()) fun _ (nv, sb) ↦ do
    guardedEq0 perform (← nv.and (← not sb))
    guardedEq0 perform (← (← not nv).and sb)

def parseJWTFieldWithQuotedValue
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (fi : QuotedFieldInput maxKVPairLen maxNameLen maxValueLen)
  (h_name  : maxNameLen  ≤ maxKVPairLen)
  (h_value : maxValueLen ≤ maxKVPairLen)
  (skipChecks         : FB bn254) :
  ClapM bn254 Unit
:= do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value fi.field fi.name fi.value fi.colonIndex fi.valueIndex skipChecks
  let perform : FB bn254 ← not skipChecks
  -- Check 0+1: field[value_index - 1] == '"' and field[value_index + value_len] == '"'
  -- (quotes around the value)
  checkValueQuotes fi.field.data perform fi.valueIndex fi.value.len
  -- Check 2: whitespace in the three "gap" zones
  checkWhitespaceZonesQuoted fi.field.data perform fi.name.len fi.colonIndex fi.valueIndex
    fi.value.len fi.field.len
  -- Check 3: name/value content positions agree exactly with fieldStringBodies
  checkStringBodies perform fi.name.len fi.valueIndex fi.value.len fi.fieldStringBodies.data

private lemma checkValueQuotes.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {perform valueIndex valueLen : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {perform_val : Bool}
  {value_index_val value_len : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkValueQuotes field_data perform valueIndex valueLen)
    state ()
    ( ( (value_index_val - 1).val < maxKVPairLen ∧
        (perform_val = true → field_vals.getD (value_index_val - 1).val 0 = 34) ) ∧
      ( (value_index_val + value_len).val < maxKVPairLen ∧
        (perform_val = true → field_vals.getD (value_index_val + value_len).val 0 = 34) ) )
:= by
  unfold checkValueQuotes
  step mkF.convertsM as one
  step mkSub.convertsM h_vi h_one as s1
  simp only [true_implies]
  have hSel1 := selectArrayValue.convertsM h_s1 h_field_val h_maxKV
  have hCheck1 := convertsM_bind_and (function := fun delimChar => mkF (34 : ZMod bn254) >>= fun c =>
      guardedAssertEq perform delimChar c)
    hSel1 (parseJWTFieldSharedLogic.assertEqLit_convertsM (lit := (34 : ZMod bn254)) hSel1.result
      (converts_skip hSel1 h_perform))
  -- Abstract `hCheck1`'s action into an opaque local constant before reframing hypotheses
  -- through it: `converts_skip hCheck1 h` otherwise has to spell out
  -- `(selectArrayValue ... >>= fun delimChar => mkF 34 >>= ...).getState s1_state` afresh at
  -- every call, and the kernel pays to re-reduce that nested term each time — the same `whnf`
  -- wall as a concrete gadget's `getResult`/`getState` left as a term (see
  -- `docs/proving-circuits.md §Using a range established earlier`, last note).
  generalize hAct1 : (selectArrayValue maxKVPairLen field_data s1_result >>= fun delimChar =>
      mkF (34 : ZMod bn254) >>= fun c => guardedAssertEq perform delimChar c) = act1 at hCheck1
  replace h_field_val := converts_skip hCheck1 h_field_val
  replace h_perform := converts_skip hCheck1 h_perform
  replace h_vi := converts_skip hCheck1 h_vi
  replace h_vl := converts_skip hCheck1 h_vl
  -- `hS2` is built as a standalone term (not via `step`), since the live goal is not being
  -- consumed here — `hCheck1`/`hCheck2` are assembled independently and only combined at the end.
  have hS2 := mkAdd.convertsM h_vi h_vl
  have hSel2 := selectArrayValue.convertsM hS2.result (converts_skip hS2 h_field_val) h_maxKV
  have hCheck2Core := convertsM_bind_and (function := fun delimChar => mkF (34 : ZMod bn254) >>= fun c =>
      guardedAssertEq perform delimChar c)
    hSel2 (parseJWTFieldSharedLogic.assertEqLit_convertsM (lit := (34 : ZMod bn254)) hSel2.result
      (converts_skip hSel2 (converts_skip hS2 h_perform)))
  have hCheck2 := convertsM_bind_and (function := fun s2 =>
      selectArrayValue maxKVPairLen field_data s2 >>= fun delimChar =>
        mkF (34 : ZMod bn254) >>= fun c => guardedAssertEq perform delimChar c)
    hS2 hCheck2Core
  have hcomb := parseJWTFieldSharedLogic.seqUnit_convertsM hCheck1 hCheck2
  rw [← hAct1] at hcomb
  simp only [bind_assoc, true_and] at hcomb
  exact hcomb

private lemma nameColonGap_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {nameLen colonIndex : F bn254} {name_len colon_index_val : ZMod bn254}
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (anyGapZoneDef.nameColonGapDef maxKVPairLen nameLen colonIndex)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) && decide (i.val < colon_index_val.val)))
    (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen)
:= by
  unfold anyGapZoneDef.nameColonGapDef
  step mkF.convertsM as two
  step mkAdd.convertsM h_nl h_two as s
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_ci h_maxKV) rfl
  simp only [true_implies]

/-- `colonValueGapDef`'s construction: `arraySelectorComplex maxKVPairLen (colonIndex+one)
(valueIndex-one)`. -/
private lemma colonValueGap_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {colonIndex valueIndex : F bn254} {colon_index_val value_index_val : ZMod bn254}
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (anyGapZoneDef.colonValueGapDef maxKVPairLen colonIndex valueIndex)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
        decide (i.val < (value_index_val - 1).val)))
    (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
      (value_index_val - 1).val < maxKVPairLen)
:= by
  unfold anyGapZoneDef.colonValueGapDef
  step mkF.convertsM as one
  step mkAdd.convertsM h_ci h_one as s
  step mkSub.convertsM h_vi h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

/-- `valueEndGapDef`'s construction: `arraySelectorComplex maxKVPairLen ((valueIndex+valueLen)+one)
(fieldLen-one)`. -/
private lemma valueEndGap_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {valueIndex valueLen fieldLen : F bn254}
  {value_index_val value_len field_len : ZMod bn254}
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (anyGapZoneDef.valueEndGapDef maxKVPairLen valueIndex valueLen fieldLen)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ i.val) &&
        decide (i.val < (field_len - 1).val)))
    (0 < (value_index_val + (value_len + 1)).val ∧
      (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen)
:= by
  unfold anyGapZoneDef.valueEndGapDef
  step mkF.convertsM as one
  step mkAdd.convertsM h_vl h_one as t
  step mkAdd.convertsM h_vi h_t as s
  step mkSub.convertsM h_fl h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

/-- `valueEndGapDef`'s computation plus the two `zipWithM` merges, taking the name-colon and
colon-value gaps' pointwise facts as given. Proved as its own lemma (not inlined into
`anyGapZone_convertsM`'s tactic chain) so its target constraint is concrete from the start:
`step`ing a real-constraint action against a goal whose own constraint slot is still an unresolved
metavariable (as it would be mid-way through `anyGapZone_convertsM`'s outer `convertsM_bind_and`
chain) is what caused the `whnf` blowup here. -/
private lemma anyGapZoneTail_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {zoneA zoneB : FArray bn254 maxKVPairLen}
  {zoneA_val zoneB_val : Vector Bool maxKVPairLen}
  {valueIndex valueLen fieldLen : F bn254}
  {value_index_val value_len field_len : ZMod bn254}
  (h_zoneA_pw : ∀ i : Fin maxKVPairLen, Converts FB.conversion state zoneA[i] zoneA_val[i])
  (h_zoneB_pw : ∀ i : Fin maxKVPairLen, Converts FB.conversion state zoneB[i] zoneB_val[i])
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (anyGapZoneDef.valueEndGapDef maxKVPairLen valueIndex valueLen fieldLen >>= fun zoneC =>
      zoneA.zipWithM FB.or zoneB >>= fun inZoneAB =>
      inZoneAB.zipWithM FB.or zoneC)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen => zoneA_val[i] || zoneB_val[i] ||
      (decide (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    (0 < (value_index_val + (value_len + 1)).val ∧
        (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen)
:= by
  have hC := valueEndGap_convertsM h_vi h_vl h_fl h_maxKV
  replace h_zoneA_pw := fun i ↦ converts_skip hC (h_zoneA_pw i)
  replace h_zoneB_pw := fun i ↦ converts_skip hC (h_zoneB_pw i)
  have h_zoneC_pw := FArray.converts_iff_FB_converts.mp hC.result
  step hC as zoneCR
  step (convertsM_zipWithM_or_quoted h_zoneA_pw h_zoneB_pw) as inZoneAB
  replace h_zoneC_pw := fun i ↦
    converts_skip (convertsM_zipWithM_or_quoted h_zoneA_pw h_zoneB_pw) (h_zoneC_pw i)
  have h_inZoneAB_pw := FArray.converts_iff_FB_converts.mp h_inZoneAB
  apply convertsM_of_convertsM (convertsM_zipWithM_or_quoted h_inZoneAB_pw h_zoneC_pw)
  · ext i
    simp [Vector.getElem_ofFn]
  · exact iff_of_true trivial (fun _ h => h)

private lemma anyGapZone_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {nameLen colonIndex valueIndex valueLen fieldLen : F bn254}
  {name_len colon_index_val value_index_val value_len field_len : ZMod bn254}
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (anyGapZoneDef maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      (decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) && decide (i.val < colon_index_val.val)) ||
      (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
        decide (i.val < (value_index_val - 1).val)) ||
      (decide (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
      (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
        (value_index_val - 1).val < maxKVPairLen) ∧
      (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen) )
:= by
  unfold anyGapZoneDef
  have hA := nameColonGap_convertsM h_nl h_ci h_maxKV
  have h_zoneA_pw := FArray.converts_iff_FB_converts.mp hA.result
  replace h_ci := converts_skip hA h_ci
  replace h_vi := converts_skip hA h_vi
  replace h_vl := converts_skip hA h_vl
  replace h_fl := converts_skip hA h_fl
  apply convertsM_bind_and hA
  have hB := colonValueGap_convertsM h_ci h_vi h_maxKV
  replace h_zoneA_pw := fun i ↦ converts_skip hB (h_zoneA_pw i)
  have h_zoneB_pw := FArray.converts_iff_FB_converts.mp hB.result
  replace h_vi := converts_skip hB h_vi
  replace h_vl := converts_skip hB h_vl
  replace h_fl := converts_skip hB h_fl
  apply convertsM_bind_and hB
  apply convertsM_of_convertsM (anyGapZoneTail_convertsM h_zoneA_pw h_zoneB_pw h_vi h_vl h_fl h_maxKV)
  · ext i
    simp [Vector.getElem_ofFn]
  · rfl

private lemma checkWhitespaceZonesQuoted.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {perform : FB bn254}
  {nameLen colonIndex valueIndex valueLen fieldLen : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {perform_val : Bool}
  {name_len colon_index_val value_index_val value_len field_len : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkWhitespaceZonesQuoted field_data perform nameLen colonIndex valueIndex valueLen fieldLen)
    state ()
    ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
        (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
          (value_index_val - 1).val < maxKVPairLen) ∧
        (0 < (value_index_val + (value_len + 1)).val ∧
            (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen) ) ∧
      (∀ i : Fin maxKVPairLen,
        lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
      (perform_val = true → ∀ i : Fin maxKVPairLen,
        (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                decide (i.val < colon_index_val.val)) ||
             (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                decide (i.val < (value_index_val - 1).val)) ||
             (decide (0 < (value_index_val + (value_len + 1)).val ∧
                  (value_index_val + (value_len + 1)).val ≤ i.val) &&
                decide (i.val < (field_len - 1).val)))
           then (1 : ZMod bn254) else 0) *
          (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) )
:= by
  unfold checkWhitespaceZonesQuoted
  have hZones := anyGapZone_convertsM h_nl h_ci h_vi h_vl h_fl h_maxKV
  have h_field_val' := converts_skip hZones h_field_val
  have h_perform' := converts_skip hZones h_perform
  apply convertsM_bind_and hZones
  have h_inZoneF := FVec.converts_of_FArray_converts hZones.result
  have h_pair := fun i : Fin maxKVPairLen => FVec.converts_zip h_inZoneF h_field_val' i.isLt
  apply convertsM_of_convertsM
    (convertsM_foldlM_ctx_constraints (C_ctx := FB.conversion) (C_acc := FUnit.conversion)
      (init_val := ())
      (f_spec := fun (_ : Bool) (_ : Unit) (_ : ZMod bn254 × ZMod bn254) => ())
      (step_constraints := fun (g : Bool) (xv : ZMod bn254 × ZMod bn254) =>
        (lessThan.lessThanOk 8 8 xv.2 ∧ lessThan.lessThanOk 8 xv.2 14) ∧
        (g = true → xv.1 * (if ((lessThan.lessThanRaw 8 8 xv.2 && lessThan.lessThanRaw 8 xv.2 14) ||
          xv.2 == 32) then (0 : ZMod bn254) else 1) = 0))
      h_perform' h_pair FUnit.converts
      (fun h_ctx h_acc h_x => guardedWhitespaceCheck_convertsM h_ctx
        (FPair.converts_fst h_x) (FPair.converts_snd h_x)))
  · rfl
  · rw [forall_and_guard_comm]
    constructor
    · rintro ⟨hA, hB⟩
      refine ⟨fun i => ?_, fun hg i => ?_⟩
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hA i
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hB hg i
    · rintro ⟨hA, hB⟩
      refine ⟨fun i => ?_, fun hg i => ?_⟩
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hA i
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hB hg i

private lemma checkStringBodies.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {perform nameLen valueIndex valueLen : F bn254}
  {sb_data : FArray bn254 maxKVPairLen}
  {perform_val : Bool} {name_len value_index_val value_len : ZMod bn254}
  {sb_vals : Vector Bool maxKVPairLen}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_sb : Converts FArray.conversion state sb_data sb_vals)
  (h_maxKV : maxKVPairLen < bn254) (hw : 2 ^ (minBits' maxKVPairLen + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (checkStringBodies perform nameLen valueIndex valueLen sb_data)
    state ()
    ( ( (name_len + 1).val < 2 ^ minBits' maxKVPairLen ∧
        (1 : ZMod bn254).val < maxKVPairLen ∧ (1 : ZMod bn254).val < (name_len + 1).val ) ∧
      ( (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ) ∧
      True ∧
      (∀ i : Fin maxKVPairLen,
        (perform_val = true →
          ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
            (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
          = true → sb_vals[i] = true) ∧
        (perform_val = true → sb_vals[i] = true →
          ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
            (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
          = true) ) )
:= by
  unfold checkStringBodies
  step mkF.convertsM as one
  step mkAdd.convertsM h_nl h_one as nameEnd
  simp only [true_implies]
  have hNameSel := arraySelector.convertsM h_one h_nameEnd h_maxKV hw
  clear h_nl h_one h_nameEnd
  replace h_vi := converts_skip hNameSel h_vi
  replace h_vl := converts_skip hNameSel h_vl
  replace h_perform := converts_skip hNameSel h_perform
  replace h_sb := converts_skip hNameSel h_sb
  apply convertsM_bind_and hNameSel
  have h_nameSel_result := hNameSel.result
  clear hNameSel
  step mkAdd.convertsM h_vi h_vl as valueEnd
  simp only [true_implies]
  have hValueSel := arraySelector.convertsM h_vi h_valueEnd h_maxKV hw
  clear h_valueEnd
  have h_nameSel_pw := FArray.converts_iff_FB_converts.mp (converts_skip hValueSel h_nameSel_result)
  replace h_perform := converts_skip hValueSel h_perform
  replace h_sb := converts_skip hValueSel h_sb
  apply convertsM_bind_and hValueSel
  have h_valueSel_pw := FArray.converts_iff_FB_converts.mp hValueSel.result
  have h_nameOrValue := convertsM_zipWithM_or_quoted h_nameSel_pw h_valueSel_pw
  replace h_perform := converts_skip h_nameOrValue h_perform
  replace h_sb := converts_skip h_nameOrValue h_sb
  apply convertsM_bind_and h_nameOrValue
  have h_pair := fun i : Fin maxKVPairLen => FBPair.converts_zip h_nameOrValue.result h_sb i.isLt
  apply convertsM_of_convertsM
    (convertsM_foldlM_ctx_constraints (C_ctx := FB.conversion) (C_acc := FUnit.conversion)
      (init_val := ())
      (f_spec := fun (_ : Bool) (_ : Unit) (_ : Bool × Bool) => ())
      (step_constraints := fun (g : Bool) (xv : Bool × Bool) =>
        (g = true → xv.1 = true → xv.2 = true) ∧ (g = true → xv.2 = true → xv.1 = true))
      h_perform h_pair FUnit.converts
      (fun h_ctx h_acc h_x => guardedStringBodyCheck_convertsM h_ctx
        (FBPair.converts_fst h_x) (FBPair.converts_snd h_x)))
  · rfl
  · simp [Vector.getElem_zip, Vector.getElem_ofFn, Fin.getElem_fin]

namespace parseJWTFieldWithQuotedValue

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (sb_vals : Vector Bool maxKVPairLen)
  (colon_index_val value_index_val : ZMod bn254)
  (skipChecks_val  : Bool) :
  Prop
:=
  let charBeforeValue := field_vals.getD (value_index_val - 1).val 0 |>.val
  let charAfterValue := field_vals.getD (value_index_val + value_len).val 0 |>.val
  ¬skipChecks_val →
    parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len
      value_vals
      value_len
      colon_index_val
      value_index_val
      false
    ∧
    charBeforeValue = /- quotes -/ 34 ∧
    charAfterValue = /- quotes -/ 34 ∧
    (∀ i : Fin maxKVPairLen,
      (name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val ∨
      (colon_index_val + 1).val ≤ i.val ∧ i.val < (value_index_val - 1).val ∨
      (value_index_val + value_len + 1).val ≤ i.val ∧ i.val < (field_len - 1).val →
        isWs field_vals[i].val
    ) ∧
    ∀ i : Fin maxKVPairLen,
      1 ≤ i.val ∧ i.val < name_len.val + 1 ∨
      value_index_val.val ≤ i.val ∧ i.val < (value_index_val + value_len).val ↔
        sb_vals[i] = true

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  -- Circuit arguments
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len_lt  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len_lt : maxValueLen ≤ maxKVPairLen)
  -- Needed by `hashBytesToField.convertsM` (`numBytes ≤ 1953`) and, via `h_name_len_lt` /
  -- `h_value_len_lt` and `maxKVPairLen ≤ 1953 ≪ bn254`, by `isSubstring.convertsM`'s
  -- `m ≤ 1953`, `n < bn254` and `2 ^ (minBits' n + 1) < bn254` for both substring checks.
  (h_len_bound    : maxKVPairLen ≤ 1953)
  {quoted : QuotedFieldInput maxKVPairLen maxNameLen maxValueLen}
  {skipChecks  : FB bn254}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {sb_vals : Vector Bool maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  {skipChecks_val  : Bool}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state quoted.field.data field_vals)
  (h_sb_val : Converts FArray.conversion state quoted.fieldStringBodies.data sb_vals)
  (h_field_len : Converts F.conversion state quoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state quoted.name.data name_vals)
  (h_name_len : Converts F.conversion state quoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state quoted.value.data value_vals)
  (h_value_len : Converts F.conversion state quoted.value.len value_len)
  (h_ci : Converts F.conversion state quoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state quoted.valueIndex value_index_val)
  (h_sk : Converts FB.conversion state skipChecks skipChecks_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20) :
  ConvertsM FUnit.conversion
    (parseJWTFieldWithQuotedValue quoted h_name_len_lt h_value_len_lt
      skipChecks
    )
    state
    ()
    ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
      (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
      (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

      (value_index_val - 1).val < maxKVPairLen ∧
      (value_index_val + value_len).val < maxKVPairLen ∧
      0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen ∧
      0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧ (value_index_val - 1).val < maxKVPairLen ∧
      0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧ (field_len - 1).val < maxKVPairLen ∧
      1 < maxKVPairLen ∧ 1 < (name_len + 1).val ∧
      value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        sb_vals
        colon_index_val
        value_index_val
        skipChecks_val
    )
:= by
  have hw20 : (2:ℕ) ^ (20 + 1) < bn254 := by decide
  have h_maxKV_bn254 : maxKVPairLen < bn254 := by
    have h1953 : (1953:ℕ) < bn254 := by decide
    omega
  have hw_minBits : 2 ^ (minBits' maxKVPairLen + 1) < bn254 := by
    have h11 : minBits' maxKVPairLen ≤ 11 := by
      unfold minBits'
      split
      · omega
      · rename_i hx
        have hx11 : maxKVPairLen < 2 ^ 11 := by omega
        have := (Nat.log2_lt hx).mpr hx11
        omega
    have h2 : (2:ℕ) ^ (minBits' maxKVPairLen + 1) ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4096 : (2:ℕ)^12 < bn254 := by decide
    omega
  unfold parseJWTFieldWithQuotedValue
  refine convertsM_of_convertsM
    (constraints1 :=
      ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
        (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
        (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧
        name_len.val + 1 < maxKVPairLen ∧
        colon_index_val.val < maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen ∧
        0 < name_len.val ∧
        (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧
        value_index_val.val < (value_index_val + value_len).val ∧
        0 < value_len.val ∧
        parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len value_vals value_len
          colon_index_val value_index_val skipChecks_val ) ∧
      ( ( (value_index_val - 1).val < maxKVPairLen ∧
          ((!skipChecks_val) = true → field_vals.getD (value_index_val - 1).val 0 = 34) ) ∧
        ( (value_index_val + value_len).val < maxKVPairLen ∧
          ((!skipChecks_val) = true → field_vals.getD (value_index_val + value_len).val 0 = 34) ) ) ∧
      ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
          (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
            (value_index_val - 1).val < maxKVPairLen) ∧
          (0 < (value_index_val + (value_len + 1)).val ∧
              (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
            (field_len - 1).val < maxKVPairLen) ) ∧
        (∀ i : Fin maxKVPairLen,
          lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
        ((!skipChecks_val) = true → ∀ i : Fin maxKVPairLen,
          (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
               (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
               (decide (0 < (value_index_val + (value_len + 1)).val ∧
                    (value_index_val + (value_len + 1)).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val)))
             then (1 : ZMod bn254) else 0) *
            (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                  field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) ) ∧
      ( ( (name_len + 1).val < 2 ^ minBits' maxKVPairLen ∧
          (1 : ZMod bn254).val < maxKVPairLen ∧ (1 : ZMod bn254).val < (name_len + 1).val ) ∧
        ( (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
          value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ) ∧
        True ∧
        (∀ i : Fin maxKVPairLen,
          ((!skipChecks_val) = true →
            ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
              (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
            = true → sb_vals[i] = true) ∧
          ((!skipChecks_val) = true → sb_vals[i] = true →
            ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
              (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
            = true) ) )
    )
    ?_ rfl ?hiff
  · have hSL := parseJWTFieldSharedLogic.convertsM h_H h_name_len_lt h_value_len_lt h_len_bound
      h_field_val h_field_len h_name_val h_name_len h_value_val h_value_len h_ci h_vi h_sk
      h_name_len_w h_colon_index_w h_value_index_w h_field_len_w h_sum_len_w
    replace h_field_val := converts_skip hSL h_field_val
    replace h_name_val := converts_skip hSL h_name_val
    replace h_name_len := converts_skip hSL h_name_len
    replace h_ci := converts_skip hSL h_ci
    replace h_vi := converts_skip hSL h_vi
    replace h_value_val := converts_skip hSL h_value_val
    replace h_value_len := converts_skip hSL h_value_len
    replace h_field_len := converts_skip hSL h_field_len
    replace h_sk := converts_skip hSL h_sk
    replace h_sb_val := converts_skip hSL h_sb_val
    apply convertsM_bind_and hSL
    clear hSL
    have hNot := not.convertsM h_sk
    replace h_field_val := converts_skip hNot h_field_val
    replace h_name_val := converts_skip hNot h_name_val
    replace h_name_len := converts_skip hNot h_name_len
    replace h_ci := converts_skip hNot h_ci
    replace h_vi := converts_skip hNot h_vi
    replace h_value_val := converts_skip hNot h_value_val
    replace h_value_len := converts_skip hNot h_value_len
    replace h_field_len := converts_skip hNot h_field_len
    replace h_sb_val := converts_skip hNot h_sb_val
    refine convertsM_bind hNot ?_ (fun _ => trivial)
    simp only [true_implies]
    have h_perform := hNot.result
    clear hNot
    have hCheckValueQuotes := checkValueQuotes.convertsM h_field_val h_perform h_vi h_value_len
      h_maxKV_bn254
    replace h_field_val := converts_skip hCheckValueQuotes h_field_val
    replace h_vi := converts_skip hCheckValueQuotes h_vi
    replace h_value_len := converts_skip hCheckValueQuotes h_value_len
    replace h_name_len := converts_skip hCheckValueQuotes h_name_len
    replace h_ci := converts_skip hCheckValueQuotes h_ci
    replace h_field_len := converts_skip hCheckValueQuotes h_field_len
    replace h_sb_val := converts_skip hCheckValueQuotes h_sb_val
    replace h_perform := converts_skip hCheckValueQuotes h_perform
    apply convertsM_bind_and hCheckValueQuotes
    clear hCheckValueQuotes
    have hCheckWS := checkWhitespaceZonesQuoted.convertsM h_field_val h_perform h_name_len h_ci h_vi
      h_value_len h_field_len h_maxKV_bn254
    replace h_vi := converts_skip hCheckWS h_vi
    replace h_value_len := converts_skip hCheckWS h_value_len
    replace h_name_len := converts_skip hCheckWS h_name_len
    replace h_sb_val := converts_skip hCheckWS h_sb_val
    replace h_perform := converts_skip hCheckWS h_perform
    apply convertsM_bind_and hCheckWS
    clear hCheckWS
    exact checkStringBodies.convertsM h_perform h_name_len h_vi h_value_len h_sb_val h_maxKV_bn254
      hw_minBits
  case hiff =>
    have hskf_of_neg : ¬skipChecks_val → skipChecks_val = false := by
      intro hneg
      revert hneg
      cases skipChecks_val <;> simp
    have h2v : (2 : ZMod bn254).val = 2 := by decide
    have h1v : (1 : ZMod bn254).val = 1 := by decide
    have h_vlp1_assoc : value_index_val + (value_len + 1) = value_index_val + value_len + 1 := by
      ring
    have h20lt : (2:ℕ) ^ 20 < bn254 := by decide
    have h_nl1 : (name_len + 1).val = name_len.val + 1 := by
      have hlt : name_len.val + (1 : ZMod bn254).val < bn254 := by rw [h1v]; omega
      rw [ZMod.val_add_of_lt hlt, h1v]
    have h_name2 : (name_len + 2).val = name_len.val + 2 := by
      have hlt : name_len.val + (2 : ZMod bn254).val < bn254 := by rw [h2v]; omega
      rw [ZMod.val_add_of_lt hlt, h2v]
    constructor
    · rintro ⟨⟨hB1, hB2, hB3, hW1, hW2, hW3, hP1, hV1, hV2, hV3, hP2, hSLparses⟩,
        ⟨⟨hQ1a, hQ1b⟩, ⟨hQ2a, hQ2b⟩⟩,
        ⟨⟨hZA, hZB, hZC⟩, hZok, hZarith⟩,
        ⟨⟨hNS1, hNS2, hNS3⟩, ⟨hVS1, hVS2, hVS3⟩, -, hSBarith⟩⟩
      refine ⟨hB1, hB2, hB3, hQ1a, hQ2a, hZA.1, hZA.2.1, hZA.2.2, hZB.1, hZB.2.1, hZB.2.2,
        ?_, ?_, ?_, ?_, ?_, hVS2, hVS3, ?_⟩
      · rw [h_vlp1_assoc] at hZC; exact hZC.1
      · rw [h_vlp1_assoc] at hZC; exact hZC.2.1
      · rw [h_vlp1_assoc] at hZC; exact hZC.2.2
      · omega
      · rw [h1v] at hNS2; omega
      · intro hneg
        have hskf := hskf_of_neg hneg
        have hguard : (!skipChecks_val) = true := by simp [hskf]
        refine ⟨fun _ => hSLparses hneg, ?_, ?_, ?_, ?_⟩
        · have h34 := hQ1b hguard
          rw [h34]; decide
        · have h34 := hQ2b hguard
          rw [h34]; decide
        · intro i hranges
          have hzarith_i := hZarith hguard i
          have hzone_true :
              ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                    decide (i.val < colon_index_val.val)) ||
                (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                    decide (i.val < (value_index_val - 1).val)) ||
                (decide (0 < (value_index_val + (value_len + 1)).val ∧
                      (value_index_val + (value_len + 1)).val ≤ i.val) &&
                    decide (i.val < (field_len - 1).val))) = true := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            rcases hranges with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl (Or.inl ⟨⟨hZA.1, h1⟩, h2⟩)
            · exact Or.inl (Or.inr ⟨⟨hZB.1, h1⟩, h2⟩)
            · exact Or.inr ⟨⟨hZC.1, by rw [h_vlp1_assoc]; exact h1⟩, h2⟩
          rw [hzone_true] at hzarith_i
          simp only [if_true, one_mul] at hzarith_i
          by_contra hws
          have hraw : ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
              field_vals[i] == 32) = false := by
            rw [lessThanRaw_isWs_eq_quoted (hB1 i)]
            simpa using hws
          rw [hraw] at hzarith_i
          simp at hzarith_i
        · intro i
          have hsb_i := hSBarith i
          constructor
          · intro hrange
            rcases hrange with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · refine hsb_i.1 hguard ?_
              simp only [Bool.or_eq_true]
              left
              rw [h1v, h_nl1]
              exact (xor_le_iff_interval (by omega)).mpr ⟨h1, h2⟩
            · refine hsb_i.1 hguard ?_
              simp only [Bool.or_eq_true]
              right
              exact (xor_le_iff_interval hV3).mpr ⟨h1, h2⟩
          · intro hsb
            have hor := hsb_i.2 hguard hsb
            simp only [Bool.or_eq_true] at hor
            rcases hor with h | h
            · left
              rw [h1v, h_nl1] at h
              exact (xor_le_iff_interval (by omega)).mp h
            · right
              exact (xor_le_iff_interval hV3).mp h
    · rintro ⟨hB1, hB2, hB3, hQ1a, hQ2a, hZA1, hZA2, hZA3, hZB1, hZB2, hZB3, hZC1, hZC2, hZC3,
        hNS2, hNS3, hVS1, hVS2, hparses⟩
      have hlt_minBits : maxKVPairLen < 2 ^ minBits' maxKVPairLen := by
        unfold minBits'
        split
        · rename_i h0
          simp [h0]
        · rename_i hx
          exact (Nat.log2_lt hx).mp (Nat.lt_succ_self _)
      have h0name : 0 < name_len.val := by rw [h_nl1] at hNS3; omega
      have h1name : name_len.val + 1 < maxKVPairLen := by rw [h_name2] at hZA2; omega
      have hNS1 : (name_len + 1).val < 2 ^ minBits' maxKVPairLen := by omega
      have hV1 : (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen := by omega
      have h0val : 0 < value_len.val := by
        by_contra hc
        push Not at hc
        have hv0 : value_len.val = 0 := Nat.le_zero.mp hc
        have hz : value_len = 0 := ZMod.val_injective bn254 (by simp [hv0])
        rw [hz, add_zero] at hVS2
        omega
      have hZC' : 0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen := by
        rw [h_vlp1_assoc]
        exact ⟨hZC1, by omega, hZC3⟩
      have h34 : (34 : ZMod bn254).val = 34 := by decide
      refine ⟨⟨hB1, hB2, hB3, h1name, hZA3, hZC3, h0name, hV1, hVS1, hVS2, h0val, ?_⟩,
        ⟨⟨hQ1a, ?_⟩, ⟨hQ2a, ?_⟩⟩,
        ⟨⟨⟨hZA1, hZA2, hZA3⟩, ⟨hZB1, hZB2, hZB3⟩, hZC'⟩,
          fun i => ⟨lessThan.lessThanOk_of
            (show (8 : ZMod bn254).val < 2 ^ 8 by decide) (hB1 i) (by decide),
            lessThan.lessThanOk_of (hB1 i) (show (14 : ZMod bn254).val < 2 ^ 8 by decide) (by decide)⟩, ?_⟩,
        ⟨hNS1, by rw [h1v]; omega, by rw [h1v]; omega⟩,
        ⟨hV1, hVS1, hVS2⟩, trivial, ?_⟩
      · intro hneg
        exact (hparses hneg).1 (by decide)
      · intro hguard
        have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
        have h34eq := (hparses hneg).2.1
        exact ZMod.val_injective bn254 (by rw [h34, h34eq])
      · intro hguard
        have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
        have h34eq := (hparses hneg).2.2.1
        exact ZMod.val_injective bn254 (by rw [h34, h34eq])
      · intro hguard i
        by_cases hzone :
            ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
              (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
              (decide (0 < (value_index_val + (value_len + 1)).val ∧
                    (value_index_val + (value_len + 1)).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val))) = true
        · have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
          have hranges_i :
              ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
              ((colon_index_val + 1).val ≤ i.val ∧ i.val < (value_index_val - 1).val) ∨
              ((value_index_val + (value_len + 1)).val ≤ i.val ∧ i.val < (field_len - 1).val) := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hzone
            rcases hzone with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · exact Or.inl ⟨h1.2, h2⟩
            · exact Or.inr (Or.inl ⟨h1.2, h2⟩)
            · exact Or.inr (Or.inr ⟨h1.2, h2⟩)
          rw [h_vlp1_assoc] at hranges_i
          have hws_i := (hparses hneg).2.2.2.1 i (by
            rcases hranges_i with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
          rw [hzone]
          rw [lessThanRaw_isWs_eq_quoted (hB1 i)]
          simpa using hws_i
        · simp only [Bool.not_eq_true] at hzone
          rw [hzone]
          simp
      · intro i
        constructor
        · intro hguard hxor
          have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
          apply ((hparses hneg).2.2.2.2 i).mp
          simp only [Bool.or_eq_true] at hxor
          rcases hxor with h | h
          · left
            have h' := (xor_le_iff_interval (a := (1:ZMod bn254).val) (b := (name_len + 1).val)
              (by rw [h1v, h_nl1]; omega)).mp h
            rwa [h1v, h_nl1] at h'
          · right
            exact (xor_le_iff_interval hVS2).mp h
        · intro hguard hsb
          have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
          have hor := ((hparses hneg).2.2.2.2 i).mpr hsb
          simp only [Bool.or_eq_true]
          rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left
            have : (decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) = true :=
              (xor_le_iff_interval (a := (1:ZMod bn254).val) (b := (name_len + 1).val)
                (by rw [h1v]; omega)).mpr (by rw [h1v]; omega)
            simpa using this
          · right
            exact (xor_le_iff_interval hVS2).mpr ⟨h1, h2⟩

theorem sound {nF nN nV} (field name value : String)
  (stringBodies : Vector Bool nF)
  (colonIndex valueIndex : ZMod bn254)
  (h_fieldLen : field.length ≤ nF) (h_nameLen : name.length ≤ nN) (h_valueLen : value.length ≤ nV)
  (h_namePos : 0 < name.length) (h_valuePos : 0 < value.length)
  (h_nF_name : 1 < nF) (h_valueIndex : valueIndex.val < nF)
  (h_nm_name : nF + nN < bn254) (h_nm_value : nF + nV < bn254)
  (h_fieldBytes : ∀ c ∈ field.toList, c.toNat < 256)
  (h_nameBytes : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_valueBytes : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_bad :
    ¬ (1 + name.length ≤ field.length ∧ name.toList <+: field.toList.drop 1) ∨
    ¬ (valueIndex.val + value.length ≤ field.length ∧
        value.toList <+: field.toList.drop valueIndex.val
      )
  )
  :
  randomOracle.toOuterMeasure
    {f |
      parses (skipChecks_val := false) (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        stringBodies
        colonIndex
        valueIndex
        } ≤ (((nF - 1) + (max nN nV - 1) + 50 : ℕ) : ENNReal) / bn254
:= by
  have h_sub : {f : Query → ZMod bn254 |
      parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length stringBodies colonIndex
        valueIndex} ⊆
      {f | parseJWTFieldSharedLogic.parses (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex
        false} := by
    intro f hf
    unfold parses at hf
    obtain ⟨h1, -, -, -, -⟩ := hf (by decide)
    exact h1
  exact (MeasureTheory.measure_mono h_sub).trans
    (parseJWTFieldSharedLogic.sound field name value colonIndex valueIndex h_fieldLen h_nameLen
      h_valueLen h_namePos h_valuePos h_nF_name h_valueIndex h_nm_name h_nm_value h_fieldBytes
      h_nameBytes h_valueBytes h_bad)

theorem complete {nF nN nV} (field name value : String)
  (colonIndex valueIndex : ZMod bn254)
  (stringBodies : Vector Bool nF)
  (h_fieldLen : field.length ≤ nF)
  (h_nameLen : name.length ≤ nN)
  (h_valueLen : value.length ≤ nV)
  (h_namePos : 0 < name.length)
  (h_valuePos : 0 < value.length)
  (h_nF_name : 1 < nF)
  (h_nm_name : nF + nN < bn254)
  (h_nm_value : nF + nV < bn254)
  (h_fieldBytes : ∀ c ∈ field.toList, c.toNat < 256)
  (h_nameBytes : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_valueBytes : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_fit_name : 1 + name.length ≤ field.length)
  (h_pre_name : name.toList <+: field.toList.drop 1)
  (h_fit_val : valueIndex.val + value.length ≤ field.length)
  (h_pre_val : value.toList <+: field.toList.drop valueIndex.val)
  (h_colon_order : name.length < colonIndex.val)
  (h_value_order : colonIndex.val < valueIndex.val)
  (h_open_quote : field.toList[0]? = some '\"')
  (h_close_quote : field.toList[name.length + 1]? = some '\"')
  (h_quoted₁ : field.toList[(valueIndex - 1).val]? = some '\"')
  (h_quoted₂ : field.toList[(valueIndex + value.length).val]? = some '\"')
  (h_colon : field.toList[colonIndex.val]? = some ':')
  (h_last_char : field.toList[field.length - 1]? = some ',' ∨
    field.toList[field.length - 1]? = some '}')
  (h_ws_zones : ∀ i,
    name.length + 2 ≤ i ∧ i < colonIndex.val ∨
    colonIndex.val + 1 ≤ i ∧ i < (valueIndex - 1).val ∨
    valueIndex.val + value.length + 1 ≤ i ∧ i < field.length - 1 →
    (field.toList[i]?.elim false (isWs ∘ Char.toNat) : Prop)
  )
  (h_stringBodies : ∀ i : ℕ,
    1 ≤ i ∧ i < name.length + 1 ∨
    valueIndex.val ≤ i ∧ i < valueIndex.val + value.length ↔
      stringBodies.toList[i]? = some true
  )
  :
  randomOracle.toOuterMeasure
    {f |
      ¬parses (skipChecks_val := false) (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        stringBodies
        colonIndex
        valueIndex
    }
      ≤ ((2 * (nF - 1) + 100 : ℕ) : ENNReal) / bn254
:= by
  have h1v : (1 : ZMod bn254).val = 1 := by decide
  have h2v : (2 : ZMod bn254).val = 2 := by decide
  have h256 : (256 : ℕ) < bn254 := by decide
  have hUInt8lt : ∀ c : Char, c.toUInt8.toNat < bn254 := fun c =>
    lt_trans (UInt8.toNat_lt_size c.toUInt8) h256
  have hvi_lt_fieldLen : valueIndex.val < field.length := by omega
  have h_vi_nF : valueIndex.val < nF := by omega
  have h_nl_lt : name.length < bn254 := by omega
  have h_nl_val : (name.length : ZMod bn254).val = name.length := ZMod.val_natCast_of_lt h_nl_lt
  have h_nl2_val : ((name.length : ZMod bn254) + 2).val = name.length + 2 := by
    rw [ZMod.val_add_of_lt (show (name.length : ZMod bn254).val + (2 : ZMod bn254).val < bn254 by
      rw [h_nl_val, h2v]; omega), h_nl_val, h2v]
  have h_vl_lt : value.length < bn254 := by omega
  have h_vl_val : (value.length : ZMod bn254).val = value.length := ZMod.val_natCast_of_lt h_vl_lt
  have h_vi_vl_val : (valueIndex + (value.length : ZMod bn254)).val
      = valueIndex.val + value.length := by
    rw [ZMod.val_add_of_lt (show valueIndex.val + (value.length : ZMod bn254).val < bn254 by
      rw [h_vl_val]; omega), h_vl_val]
  have h_fl_lt : field.length < bn254 := by omega
  have h_fl_val : (field.length : ZMod bn254).val = field.length := ZMod.val_natCast_of_lt h_fl_lt
  have h_fl1_val : ((field.length : ZMod bn254) - 1).val = field.length - 1 := by
    rw [ZMod.val_sub (by rw [h_fl_val, h1v]; omega), h_fl_val, h1v]
  have hvi_ge1 : 1 ≤ valueIndex.val := by omega
  have h_vim1_val : (valueIndex - 1).val = valueIndex.val - 1 := by
    rw [ZMod.val_sub (by rw [h1v]; omega), h1v]
  have h_ci1_val : (colonIndex + 1).val = colonIndex.val + 1 := by
    rw [ZMod.val_add_of_lt (show colonIndex.val + (1 : ZMod bn254).val < bn254 by
      rw [h1v]; omega), h1v]
  have h_vlp1_val : (valueIndex + (value.length : ZMod bn254) + 1).val
      = valueIndex.val + value.length + 1 := by
    rw [ZMod.val_add_of_lt
      (show (valueIndex + (value.length : ZMod bn254)).val + (1 : ZMod bn254).val < bn254 by
        rw [h_vi_vl_val, h1v]; omega), h_vi_vl_val, h1v]
  -- The two quote checks, proved unconditionally (independent of the random oracle).
  have hw_q1 : (valueIndex - 1).val < nF := by rw [h_vim1_val]; omega
  have hs_q1 : (valueIndex - 1).val < field.toList.length := by
    rw [String.length_toList, h_vim1_val]; omega
  have hQ1 : ((encodeV (p := bn254) nF field).getD (valueIndex - 1).val 0).val = 34 := by
    rw [parseJWTFieldSharedLogic.encodeV_getD_of_lt hw_q1 hs_q1, List.getD_eq_getElem?_getD,
      h_quoted₁]
    decide
  -- The index at `h_quoted₂` is only ever a successful list lookup when it's in bounds — `h_fit_val`
  -- alone only gives `≤ field.length`, not the strict bound needed here.
  have hs_q2 : (valueIndex + (value.length : ZMod bn254)).val < field.toList.length := by
    by_contra hcon
    push Not at hcon
    rw [List.getElem?_eq_none hcon] at h_quoted₂
    exact absurd h_quoted₂ (by simp)
  have hw_q2 : (valueIndex + (value.length : ZMod bn254)).val < nF := by
    have := hs_q2
    rw [String.length_toList] at this
    omega
  have hQ2 : ((encodeV (p := bn254) nF field).getD
      (valueIndex + (value.length : ZMod bn254)).val 0).val = 34 := by
    rw [parseJWTFieldSharedLogic.encodeV_getD_of_lt hw_q2 hs_q2, List.getD_eq_getElem?_getD,
      h_quoted₂]
    decide
  -- The whitespace-zones conjunct, proved unconditionally.
  have hWS : ∀ i : Fin nF,
      (((name.length : ZMod bn254) + 2).val ≤ i.val ∧ i.val < colonIndex.val) ∨
        ((colonIndex + 1).val ≤ i.val ∧ i.val < (valueIndex - 1).val) ∨
        ((valueIndex + (value.length : ZMod bn254) + 1).val ≤ i.val ∧
          i.val < ((field.length : ZMod bn254) - 1).val) →
      isWs ((encodeV (p := bn254) nF field)[i]).val := by
    intro i hranges
    rw [h_nl2_val, h_ci1_val, h_vlp1_val, h_fl1_val] at hranges
    have hi_lt_fieldLen : i.val < field.length := by
      rcases hranges with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hi_lt_toList : i.val < field.toList.length := by
      rw [String.length_toList]; exact hi_lt_fieldLen
    have hws := h_ws_zones i.val hranges
    have hgetElem : (encodeV (p := bn254) nF field)[i] =
        (((field.toList[i.val]'hi_lt_toList).toUInt8.toNat : ℕ) : ZMod bn254) :=
      encodeV_getElem_of_lt i.isLt hi_lt_toList
    rw [hgetElem, ZMod.val_natCast_of_lt (hUInt8lt _)]
    have hsome : field.toList[i.val]? = some (field.toList[i.val]'hi_lt_toList) :=
      List.getElem?_eq_getElem hi_lt_toList
    rw [hsome] at hws
    rw [toUInt8_toNat_of_lt (h_fieldBytes _ (List.getElem_mem hi_lt_toList))]
    simpa using hws
  -- The string-body agreement conjunct, proved unconditionally.
  have hSB : ∀ i : Fin nF,
      (1 ≤ i.val ∧ i.val < (name.length : ZMod bn254).val + 1 ∨
        valueIndex.val ≤ i.val ∧
          i.val < (valueIndex + (value.length : ZMod bn254)).val) ↔
        stringBodies[i] = true := by
    intro i
    have hbridge : stringBodies.toList[i.val]? = some true ↔ stringBodies[i] = true := by
      rw [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt, Fin.getElem_fin]
      exact Option.some_inj
    rw [h_nl_val, h_vi_vl_val, ← hbridge]
    exact h_stringBodies i.val
  -- `parses` reduces to exactly `parseJWTFieldSharedLogic.parses`, given the above: the four extra
  -- conjuncts hold for every `f`, so `¬parses` is no weaker than `¬parseJWTFieldSharedLogic.parses`.
  have h_sub : {f : Query → ZMod bn254 |
      ¬parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length stringBodies colonIndex
        valueIndex} ⊆
      {f | ¬parseJWTFieldSharedLogic.parses (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex
        false} := by
    intro f hf hP1
    apply hf
    unfold parses
    exact fun _ => ⟨hP1, hQ1, hQ2, hWS, hSB⟩
  exact (MeasureTheory.measure_mono h_sub).trans
    (parseJWTFieldSharedLogic.complete field name value colonIndex valueIndex h_fieldLen h_nameLen
      h_valueLen h_namePos h_valuePos h_nF_name h_nm_name h_nm_value h_fieldBytes h_nameBytes
      h_valueBytes h_fit_name h_pre_name h_fit_val h_pre_val h_colon_order h_value_order
      h_open_quote h_close_quote h_colon h_last_char)

end parseJWTFieldWithQuotedValue
