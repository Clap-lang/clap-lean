import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Gate.isZero
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Core.FUnit.guardedAssertEq
import Mathlib.Data.List.GetD
import Clap.Lang.Data.JWT.Scaffold.parseJWTFieldSharedLogic

-- Poseidon is opaque to these proofs, as in HashToField/hashElemsToField.lean and
-- FString/isSubstring.lean (every gadget here routes through `hashBytesToField`).
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

namespace Clap.Lang

open Primes

/-- Checks 0–2: `name_len < colon_index < value_index` and `field_len > name_len + value_len`,
each guarded by `perform`. Factored out so each comparison is a single atomic step in the bind
tree that assembles `parseJWTFieldSharedLogic`'s own `convertsM` — see
`docs/proving-circuits.md §A long step proof takes minutes` for why that matters here. -/
private def checkIndexOrdering
  (name_len colon_index value_index field_len value_len perform : F bn254) :
  ClapM bn254 Unit
:= do
  guardedEq0 perform (← not (← lessThan 20 name_len colon_index))
  guardedEq0 perform (← not (← lessThan 20 colon_index value_index))
  guardedEq0 perform (← not (← greaterThan 20 field_len (← name_len + value_len)))

/-- The shared shape of checks (3, 4) and (6, 7): the character of `field` at `idx` equals the
literal `lit` (guarded), and `substr` is a Fiat-Shamir substring of `field` starting at `start`
(also guarded). Instantiated with `(idx, lit, substr, start) := (mkF 0, '"', name, mkF 1)` for
checks 3+4 and `(colon_index, ':', value, value_index)` for checks 6+7. -/
private def checkDelimiterThenSubstring
  {maxKVPairLen maxSubLen : ℕ}
  (h_len_lt : maxSubLen ≤ maxKVPairLen)
  (field_data : FVec bn254 maxKVPairLen)
  (fieldHash : F bn254)
  (substr : FString bn254 maxSubLen)
  (idx : F bn254)
  (lit : ZMod bn254)
  (start : F bn254)
  (perform : FB bn254) :
  ClapM bn254 Unit
:= do
  let delimChar ← selectArrayValue maxKVPairLen field_data idx
  guardedAssertEq perform delimChar (← mkF lit)
  let ok ← FString.isSubstring h_len_lt field_data fieldHash substr start
  guardedEq0 perform (← not ok)

/-- Checks 3+4 with their two literal allocations (`mkF 0`, `mkF 1`) folded in, also kept opaque:
`apply convertsM_bind_and <fact>` against the live goal needs the fact's *whole* action to be a
single bind-head it can match structurally, and a fact whose action still starts with bare
`mkF 0 >>= fun idx0 => mkF 1 >>= fun one => …` forces the kernel to unfold those hash-consing
allocations to check the match — the same `whnf` wall as before, just moved one level in. -/
private def checkNameSubstring
  {maxKVPairLen maxNameLen : ℕ}
  (h_name_len_lt : maxNameLen ≤ maxKVPairLen)
  (field_data : FVec bn254 maxKVPairLen)
  (fieldHash : F bn254)
  (name : FString bn254 maxNameLen)
  (perform : FB bn254) : ClapM bn254 Unit
:= do
  let idx0 ← mkF 0
  let one ← mkF 1
  checkDelimiterThenSubstring h_name_len_lt field_data fieldHash name idx0
    ('\"'.toNat : ZMod bn254)
    one
    perform

/-- Check 5: `field[name_len + 1] = '"'`. Kept as its own opaque `def` — not for proof-structure
reasons this time (its proof, `check5_convertsM`, is a single straight-line `step` chain with no
combination issues of its own), but so the *top-level* `parseJWTFieldSharedLogic` do-block stays
small enough for the final assembly's `seqUnit_convertsM`/`convertsM_bind_and` chain to unify
against in reasonable time: inlined, checks 3–8 together are ~20 nested binds deep, which is what
made that assembly time out even after every other fix in this file. -/
private def checkNameClosingQuote
  {maxKVPairLen : ℕ}
  (field_data : FVec bn254 maxKVPairLen)
  (name_len : F bn254)
  (perform : FB bn254) :
  ClapM bn254 Unit
:= do
  let s5 ← name_len + (← mkF 1)
  let nameClosingQuote ← selectArrayValue maxKVPairLen field_data s5
  guardedAssertEq perform nameClosingQuote (← mkF (34 : ZMod bn254))

/-- Check 8: `field[field_len - 1] ∈ {',', '}'}`. Opaque for the same reason as
`checkNameClosingQuote`. -/
private def checkLastCharDelimiter
  {maxKVPairLen : ℕ}
  (field_data : FVec bn254 maxKVPairLen)
  (field_len : F bn254)
  (perform : FB bn254) :
  ClapM bn254 Unit
:= do
  let s8 ← field_len - (← mkF 1)
  let lastChar ← selectArrayValue maxKVPairLen field_data s8
  guardedEq0 perform
    (← (← lastChar - (← mkF ','.toNat)) * (← lastChar - (← mkF '}'.toNat)))

def parseJWTFieldSharedLogic
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len : maxValueLen ≤ maxKVPairLen)
  (field       : FString bn254 maxKVPairLen)
  (name        : FString bn254 maxNameLen)
  (value       : FString bn254 maxValueLen)
  (colon_index : F bn254)
  (value_index : F bn254)
  (skipChecks  : FB bn254 /- := 0 -/) -- `mkF 0` can't be assigned as a default value
  : ClapM bn254 Unit
:= do
  let perform : FB bn254 ← not skipChecks
  -- Checks 0–2: name_len < colon_index < value_index, field_len > name_len + value_len.
  -- w = 20 bits suffices for comparisons: 2^20 = 1_048_576 > any realistic JWT field length.
  -- Hardcoded in https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/jwt/ParseJWTFieldSharedLogic.circom
  checkIndexOrdering name.len colon_index value_index field.len value.len perform
  -- Pre-compute hash of field for Fiat-Shamir substring checks
  let fieldHash ← HashToField.hashBytesToField field
  -- Checks 3+4: field[0] == '"' (ASCII 34), and name is a substring of field starting at index 1
  checkNameSubstring h_name_len field.data fieldHash name perform
  -- Check 5: field[name_len + 1] == '"' (ASCII 34)
  checkNameClosingQuote field.data name.len perform
  -- Checks 6+7: field[colon_index] == ':' (ASCII 58), and value is a substring of field
  -- starting at value_index
  checkDelimiterThenSubstring h_value_len field.data fieldHash value colon_index ':'.toNat
    value_index perform
  -- Check 8: field[field_len - 1] == ',' (44) or '}' (125)
  checkLastCharDelimiter field.data field.len perform

namespace parseJWTFieldSharedLogic

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (colon_index_val value_index_val : ZMod bn254)
  (skipChecks_val  : Bool) :
  Prop
:=
  let fieldHash := HashToField.hashBytesToFieldSpec H field_vals field_len
  ¬skipChecks_val →
    name_len.val < colon_index_val.val ∧
    colon_index_val.val < value_index_val.val ∧
    field_len.val > (name_len + value_len).val ∧
    field_vals.getD 0 0 = 34 ∧
    isSubstring.accepts H field_vals fieldHash name_vals name_len 1 = true ∧
    field_vals.getD (name_len + 1).val 0 = 34 ∧
    field_vals.getD colon_index_val.val 0 = 58 ∧
    isSubstring.accepts H field_vals fieldHash value_vals value_len value_index_val = true ∧
    (field_vals.getD (field_len - 1).val 0 = 44 ∨ field_vals.getD (field_len - 1).val 0 = 125)

/-! ## Proof infrastructure for `convertsM`

One private lemma per check (or check shape) in the body's chain of nine guarded assertions.
Per `docs/proving-circuits.md §When step does not apply`, every `guardedEq0`/`guardedAssertEq`
here has a real (non-`True`) slot 5, so adjacent real-constraint binds are composed with
`convertsM_bind_and`, never `step`/`convertsM_bind`. -/

/-- Check 5, wrapped behind the opaque `checkNameClosingQuote` def (see its docstring for why). -/
private lemma checkNameClosingQuote_convertsM
  {maxKVPairLen : ℕ}
  {state : ClapMState bn254} {field_data : FVec bn254 maxKVPairLen} {name_len' perform : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {name_len : ZMod bn254} {perform_val : Bool}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_name_len : Converts F.conversion state name_len' name_len)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkNameClosingQuote field_data name_len' perform)
    state ()
    ((name_len + 1).val < maxKVPairLen ∧
      (perform_val = true → field_vals.getD (name_len + 1).val 0 = 34))
:= by
  unfold checkNameClosingQuote
  exact check5_convertsM h_field_val h_name_len h_perform h_maxKV

/-- Check 8, wrapped behind the opaque `checkLastCharDelimiter` def (see its docstring for why). -/
private lemma checkLastCharDelimiter_convertsM
  {maxKVPairLen : ℕ}
  {state : ClapMState bn254} {field_data : FVec bn254 maxKVPairLen} {field_len' perform : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {field_len : ZMod bn254} {perform_val : Bool}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_field_len : Converts F.conversion state field_len' field_len)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkLastCharDelimiter field_data field_len' perform)
    state ()
    ((field_len - 1).val < maxKVPairLen ∧
      (perform_val = true → (field_vals.getD (field_len - 1).val 0 = 44 ∨
        field_vals.getD (field_len - 1).val 0 = 125)))
:= by
  unfold checkLastCharDelimiter
  exact check8_convertsM h_field_val h_field_len h_perform h_maxKV

set_option maxHeartbeats 1000000 in
/-- Checks 0–2 combined: `checkIndexOrdering` is three `lessThan`/`greaterThan`-backed guarded
assertions in a row, each a single atomic step, combined via `seqUnit_convertsM`. -/
private lemma checkIndexOrdering_convertsM
  {state : ClapMState bn254}
  {name_len colon_index value_index field_len value_len perform : F bn254}
  {name_len_val colon_index_val value_index_val field_len_val value_len_val : ZMod bn254}
  {perform_val : Bool}
  (h_name_len : Converts F.conversion state name_len name_len_val)
  (h_ci : Converts F.conversion state colon_index colon_index_val)
  (h_vi : Converts F.conversion state value_index value_index_val)
  (h_field_len : Converts F.conversion state field_len field_len_val)
  (h_value_len : Converts F.conversion state value_len value_len_val)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_name_len_w : name_len_val.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len_val.val < 2 ^ 20)
  (h_sum_len_w : (name_len_val + value_len_val).val < 2 ^ 20)
  (hw20 : (2:ℕ) ^ (20 + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (checkIndexOrdering name_len colon_index value_index field_len value_len perform)
    state ()
    ( (perform_val = true → name_len_val.val < colon_index_val.val) ∧
      (perform_val = true → colon_index_val.val < value_index_val.val) ∧
      (perform_val = true → field_len_val.val > (name_len_val + value_len_val).val) )
:= by
  unfold checkIndexOrdering
  have hc0 := lessThanGuardedEq0_convertsM h_name_len h_ci h_perform h_name_len_w h_colon_index_w hw20
  have h_ci' := converts_skip hc0 h_ci
  have h_vi' := converts_skip hc0 h_vi
  have h_perform' := converts_skip hc0 h_perform
  have hc1 := lessThanGuardedEq0_convertsM h_ci' h_vi' h_perform' h_colon_index_w h_value_index_w hw20
  have h_field_len' := converts_skip hc1 (converts_skip hc0 h_field_len)
  have h_name_len' := converts_skip hc1 (converts_skip hc0 h_name_len)
  have h_value_len' := converts_skip hc1 (converts_skip hc0 h_value_len)
  have h_perform'' := converts_skip hc1 h_perform'
  have hc2 := check2_convertsM h_field_len' h_name_len' h_value_len' h_perform'' h_field_len_w
    h_sum_len_w hw20
  -- `seqUnit_convertsM`'s conclusion groups the three checks left-to-right
  -- (`(stmt0 >>= stmt1) >>= stmt2`), but `do`-notation threads each continuation all the way
  -- through the *previous* statement's own binds (`stmt0 >>= fun _ => stmt1 >>= fun _ => stmt2`
  -- nested at depth 3, not 1) — propositionally equal (`bind_assoc`) but not defeq without
  -- unfolding the whole monad-transformer stack, which is what timed out here before this fix.
  have hcomb := seqUnit_convertsM hc0 (seqUnit_convertsM hc1 hc2)
  simp only [bind_assoc] at hcomb
  exact hcomb

set_option maxHeartbeats 1000000 in
/-- Checks (3, 4) / (6, 7) combined: select `field[idx]`, assert it equals `lit` (guarded), then
assert `substr` is a Fiat-Shamir substring of `field` starting at `start` (also guarded). The
delimiter half is `selectArrayValue.convertsM` plus `assertEqLit_convertsM`; the substring half is
`isSubstring.convertsM` plus `check4_tail_convertsM` (shape-identical to `check7_tail_convertsM`);
`seqUnit_convertsM` composes the two halves. Instantiated at `(idx, lit, substr, start) :=
(mkF 0, '"', name, mkF 1)` for checks 3+4 and `(colon_index, ':', value, value_index)` for
checks 6+7 in the main proof below. -/
private lemma checkDelimiterThenSubstring_convertsM
  {maxKVPairLen maxSubLen : ℕ}
  {H : HashFn} (h_H : Computes H)
  (h_len_lt : maxSubLen ≤ maxKVPairLen)
  {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {fieldHash : F bn254} {substr : FString bn254 maxSubLen}
  {idx start perform : F bn254} {lit : ZMod bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {fieldHash_val : ZMod bn254}
  {substr_vals : Vector (ZMod bn254) maxSubLen} {substr_len : ZMod bn254}
  {idx_val start_val : ZMod bn254} {perform_val : Bool}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_fieldHash : Converts F.conversion state fieldHash fieldHash_val)
  (h_idx : Converts F.conversion state idx idx_val)
  (h_substr_val : Converts FVec.conversion state substr.data substr_vals)
  (h_substr_len : Converts F.conversion state substr.len substr_len)
  (h_start : Converts F.conversion state start start_val)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_maxKV : maxKVPairLen < bn254)
  (h_m : maxSubLen ≤ 1953) (hw : 2 ^ (minBits' maxKVPairLen + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (checkDelimiterThenSubstring h_len_lt field_data fieldHash substr idx lit start perform)
    state ()
    ( (idx_val.val < maxKVPairLen ∧ (perform_val = true → field_vals.getD idx_val.val 0 = lit)) ∧
      ( ( (∀ i : Fin maxSubLen, substr_vals[i].val < 2 ^ 8) ∧
          (start_val + substr_len).val < 2 ^ minBits' maxKVPairLen ∧
          start_val.val < maxKVPairLen ∧
          start_val.val < (start_val + substr_len).val ) ∧
        (perform_val = true →
          isSubstring.accepts H field_vals fieldHash_val substr_vals substr_len start_val = true) ) )
:= by
  unfold checkDelimiterThenSubstring
  have hSel := selectArrayValue.convertsM h_idx h_field_val h_maxKV
  -- `function :=` must be explicit here: `assertEqLit_convertsM`'s action mentions `hSel.result`'s
  -- *value* (`field_vals.getD idx_val.val 0`) as a concrete term, not as a bound variable, so Lean
  -- cannot invert that occurrence into a lambda on its own (the same shape of failure the
  -- `fieldHash`/`convertsM_bind_and` fix above addresses for the main proof).
  have hDelim := convertsM_bind_and (function := fun delimChar => mkF lit >>= fun c =>
      guardedAssertEq perform delimChar c)
    hSel (assertEqLit_convertsM (lit := lit) hSel.result (converts_skip hSel h_perform))
  have h_field_val' := converts_skip hDelim h_field_val
  have h_fieldHash' := converts_skip hDelim h_fieldHash
  have h_substr_val' := converts_skip hDelim h_substr_val
  have h_substr_len' := converts_skip hDelim h_substr_len
  have h_start' := converts_skip hDelim h_start
  have h_perform' := converts_skip hDelim h_perform
  have hSub := isSubstring.convertsM h_H h_len_lt h_field_val' h_fieldHash' h_substr_val' h_substr_len'
    h_start' h_m h_maxKV hw
  have hSubGuard := convertsM_bind_and (function := fun ok => not ok >>= fun c => guardedEq0 perform c)
    hSub (check4_tail_convertsM hSub.result (converts_skip hSub h_perform'))
  have hFull := seqUnit_convertsM hDelim hSubGuard
  simp only [bind_assoc] at hFull
  exact hFull

set_option maxHeartbeats 1000000 in
/-- Checks 3+4, with their two literal `idx`/`start` allocations (`mkF 0`, `mkF 1`) made explicit,
matching how `parseJWTFieldSharedLogic`'s body calls `checkDelimiterThenSubstring` for the name
field. -/
private lemma checkNameDelimiterThenSubstring_convertsM
  {maxKVPairLen maxNameLen : ℕ}
  {H : HashFn} (h_H : Computes H)
  (h_name_len_lt : maxNameLen ≤ maxKVPairLen)
  {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {fieldHash : F bn254} {name : FString bn254 maxNameLen}
  {perform : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {fieldHash_val : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen} {name_len : ZMod bn254} {perform_val : Bool}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_fieldHash : Converts F.conversion state fieldHash fieldHash_val)
  (h_name_val : Converts FVec.conversion state name.data name_vals)
  (h_name_len : Converts F.conversion state name.len name_len)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_maxKV : maxKVPairLen < bn254)
  (h_m : maxNameLen ≤ 1953) (hw : 2 ^ (minBits' maxKVPairLen + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (checkNameSubstring h_name_len_lt field_data fieldHash name perform)
    state ()
    ( (0 < maxKVPairLen ∧ (perform_val = true → field_vals.getD 0 0 = ('\"'.toNat : ZMod bn254))) ∧
      ( ( (∀ i : Fin maxNameLen, name_vals[i].val < 2 ^ 8) ∧
          ((1 : ZMod bn254) + name_len).val < 2 ^ minBits' maxKVPairLen ∧
          (1 : ZMod bn254).val < maxKVPairLen ∧
          (1 : ZMod bn254).val < ((1 : ZMod bn254) + name_len).val ) ∧
        (perform_val = true →
          isSubstring.accepts H field_vals fieldHash_val name_vals name_len 1 = true) ) )
:= by
  unfold checkNameSubstring
  step mkF.convertsM as idx0
  step mkF.convertsM as one
  apply convertsM_of_convertsM (checkDelimiterThenSubstring_convertsM h_H h_name_len_lt
    h_field_val h_fieldHash h_idx0 h_name_val h_name_len h_one h_perform h_maxKV h_m hw)
  · rfl
  · simp

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
  {field       : FString bn254 maxKVPairLen}
  {name        : FString bn254 maxNameLen}
  {value       : FString bn254 maxValueLen}
  {colon_index : F bn254}
  {value_index : F bn254}
  {skipChecks  : FB bn254}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  {skipChecks_val  : Bool}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state field.data field_vals)
  (h_field_len : Converts F.conversion state field.len field_len)
  (h_name_val : Converts FVec.conversion state name.data name_vals)
  (h_name_len : Converts F.conversion state name.len name_len)
  (h_value_val : Converts FVec.conversion state value.data value_vals)
  (h_value_len : Converts F.conversion state value.len value_len)
  (h_ci : Converts F.conversion state colon_index colon_index_val)
  (h_vi : Converts F.conversion state value_index value_index_val)
  (h_sk : Converts FB.conversion state skipChecks skipChecks_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  :
  ConvertsM FUnit.conversion
    (parseJWTFieldSharedLogic h_name_len_lt h_value_len_lt field name value
      colon_index
      value_index
      skipChecks
    )
    state
    ()
    ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
      (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
      (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

      name_len.val + 1 < maxKVPairLen ∧
      -- /- redundant -/ 0 < maxKVPairLen ∧
      colon_index_val.val < maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen ∧

      -- /- redundant -/ 1 < 2 ^ minBits' maxKVPairLen ∧
      -- /- redundant -/ (1 + name_len).val < 2 ^ minBits' maxKVPairLen ∧
      -- /- redundant -/ 1 < maxKVPairLen ∧
      -- 1 < (1 + name_len).val ∧ /- equivalent -/
      0 < name_len.val ∧

      -- /- redundant -/ value_index_val.val < 2 ^ minBits' maxKVPairLen ∧
      (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
      value_index_val.val < maxKVPairLen ∧

      value_index_val.val < (value_index_val + value_len).val ∧
      0 < value_len.val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        colon_index_val
        value_index_val
        skipChecks_val
    )
:= by
  have hw20 : (2:ℕ) ^ (20 + 1) < bn254 := by decide
  have h_maxKV_bn254 : maxKVPairLen < bn254 := by
    have h1953 : (1953:ℕ) < bn254 := by decide
    omega
  have h_maxNameLen_1953 : maxNameLen ≤ 1953 := h_name_len_lt.trans h_len_bound
  have h_maxValueLen_1953 : maxValueLen ≤ 1953 := h_value_len_lt.trans h_len_bound
  have hw_minBits : 2 ^ (minBits' maxKVPairLen + 1) < bn254 := by
    have h11 := minBits'_le_of_le_1953 h_len_bound
    have hp : (2:ℕ) ^ (minBits' maxKVPairLen + 1) ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h12 : (2:ℕ) ^ 12 < bn254 := by decide
    omega
  -- Supply `constraints1` explicitly and work directly against the live goal throughout
  -- (`apply convertsM_bind_and <fact>`, never a separately-built combined term matched against
  -- the goal at the end) — the same recipe `Base64Len/base64UrlLookup.lean` uses for this exact
  -- wall. The earlier (seqUnit_convertsM/convertsM_bind_and-built-as-a-have, then one final
  -- `exact`) version was not just slow but is the actual cause: that final match forces the
  -- kernel to decide whether the *built* term's type is defeq to the goal's by, in effect,
  -- simulating the whole `ClapM` builder computation (hence the millions of `Array.foldl`/`dite`
  -- reductions `set_option diagnostics true` showed here) — rather than the cheap, structural,
  -- one-constructor-at-a-time match `apply` does against a goal that already has the right shape.
  unfold parseJWTFieldSharedLogic
  step not.convertsM h_sk as perform
  -- `h_perform`'s ideal value is `!skipChecks_val` exactly (confirmed directly — `not.convertsM`'s
  -- stated value is `!a_val`, and nothing in `step` normalizes it further); write it the same way
  -- here so this matches `hOrder`'s (and every sub-gadget's) own inferred constraint syntactically,
  -- which is what `apply`'s unification below needs (it does not do defeq up to `decide`-unfolding).
  refine convertsM_of_convertsM (constraints1 :=
      ((Bool.not skipChecks_val = true → name_len.val < colon_index_val.val) ∧
        (Bool.not skipChecks_val = true → colon_index_val.val < value_index_val.val) ∧
        (Bool.not skipChecks_val = true → field_len.val > (name_len + value_len).val)) ∧
      ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8) ∧
        ( ( (0 < maxKVPairLen ∧
              (Bool.not skipChecks_val = true → field_vals.getD 0 0 = ('\"'.toNat : ZMod bn254))) ∧
            ( ( (∀ i : Fin maxNameLen, name_vals[i].val < 2 ^ 8) ∧
                ((1 : ZMod bn254) + name_len).val < 2 ^ minBits' maxKVPairLen ∧
                (1 : ZMod bn254).val < maxKVPairLen ∧
                (1 : ZMod bn254).val < ((1 : ZMod bn254) + name_len).val ) ∧
              (Bool.not skipChecks_val = true →
                isSubstring.accepts H field_vals
                  (HashToField.hashBytesToFieldSpec H field_vals field_len) name_vals name_len 1
                  = true) ) ) ∧
          ( ((name_len + 1).val < maxKVPairLen ∧
              (Bool.not skipChecks_val = true → field_vals.getD (name_len + 1).val 0 = 34)) ∧
            ( ( (colon_index_val.val < maxKVPairLen ∧
                  (Bool.not skipChecks_val = true → field_vals.getD colon_index_val.val 0 = 58)) ∧
                ( ( (∀ i : Fin maxValueLen, value_vals[i].val < 2 ^ 8) ∧
                    (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
                    value_index_val.val < maxKVPairLen ∧
                    value_index_val.val < (value_index_val + value_len).val ) ∧
                  (Bool.not skipChecks_val = true →
                    isSubstring.accepts H field_vals
                      (HashToField.hashBytesToFieldSpec H field_vals field_len) value_vals
                      value_len value_index_val = true) ) ) ∧
              ((field_len - 1).val < maxKVPairLen ∧
                (Bool.not skipChecks_val = true → (field_vals.getD (field_len - 1).val 0 = 44 ∨
                  field_vals.getD (field_len - 1).val 0 = 125))) ) ) ) ) )
    ?_ rfl ?hiff
  · have hOrder := checkIndexOrdering_convertsM h_name_len h_ci h_vi h_field_len h_value_len
      h_perform h_name_len_w h_colon_index_w h_value_index_w h_field_len_w h_sum_len_w hw20
    replace h_field_val := converts_skip hOrder h_field_val
    replace h_field_len := converts_skip hOrder h_field_len
    replace h_name_val := converts_skip hOrder h_name_val
    replace h_name_len := converts_skip hOrder h_name_len
    replace h_value_val := converts_skip hOrder h_value_val
    replace h_value_len := converts_skip hOrder h_value_len
    replace h_ci := converts_skip hOrder h_ci
    replace h_vi := converts_skip hOrder h_vi
    replace h_perform := converts_skip hOrder h_perform
    apply convertsM_bind_and hOrder
    clear hOrder
    generalize (checkIndexOrdering name.len colon_index value_index field.len value.len
        perform_result).getState perform_state = s0 at *
    have hHash := HashToField.hashBytesToField.convertsM h_H h_field_val h_field_len h_len_bound
    replace h_field_val := converts_skip hHash h_field_val
    replace h_field_len := converts_skip hHash h_field_len
    replace h_name_val := converts_skip hHash h_name_val
    replace h_name_len := converts_skip hHash h_name_len
    replace h_value_val := converts_skip hHash h_value_val
    replace h_value_len := converts_skip hHash h_value_len
    replace h_ci := converts_skip hHash h_ci
    replace h_vi := converts_skip hHash h_vi
    replace h_perform := converts_skip hHash h_perform
    have h_fieldHash := hHash.result
    apply convertsM_bind_and hHash
    clear hHash
    generalize (HashToField.hashBytesToField field).getState s0 = sHash at *
    generalize (HashToField.hashBytesToField field).getResult s0.numAlloc s0.σ = fieldHash at *
    have hcName := checkNameDelimiterThenSubstring_convertsM h_H h_name_len_lt h_field_val
      h_fieldHash h_name_val h_name_len h_perform h_maxKV_bn254 h_maxNameLen_1953 hw_minBits
    replace h_field_val := converts_skip hcName h_field_val
    replace h_field_len := converts_skip hcName h_field_len
    replace h_value_val := converts_skip hcName h_value_val
    replace h_value_len := converts_skip hcName h_value_len
    replace h_ci := converts_skip hcName h_ci
    replace h_vi := converts_skip hcName h_vi
    replace h_fieldHash := converts_skip hcName h_fieldHash
    replace h_perform := converts_skip hcName h_perform
    replace h_name_len := converts_skip hcName h_name_len
    apply convertsM_bind_and hcName
    clear hcName
    generalize (checkNameSubstring h_name_len_lt field.data fieldHash name
        perform_result).getState sHash = sName at *
    have hcCheck5 := checkNameClosingQuote_convertsM h_field_val h_name_len h_perform h_maxKV_bn254
    replace h_field_val := converts_skip hcCheck5 h_field_val
    replace h_field_len := converts_skip hcCheck5 h_field_len
    replace h_value_val := converts_skip hcCheck5 h_value_val
    replace h_value_len := converts_skip hcCheck5 h_value_len
    replace h_ci := converts_skip hcCheck5 h_ci
    replace h_vi := converts_skip hcCheck5 h_vi
    replace h_fieldHash := converts_skip hcCheck5 h_fieldHash
    replace h_perform := converts_skip hcCheck5 h_perform
    apply convertsM_bind_and hcCheck5
    clear hcCheck5
    generalize (checkNameClosingQuote field.data name.len perform_result).getState sName = sCheck5
      at *
    have hcValue := checkDelimiterThenSubstring_convertsM (lit := (':'.toNat : ZMod bn254)) h_H
      h_value_len_lt h_field_val h_fieldHash h_ci h_value_val h_value_len h_vi h_perform
      h_maxKV_bn254 h_maxValueLen_1953 hw_minBits
    replace h_field_val := converts_skip hcValue h_field_val
    replace h_field_len := converts_skip hcValue h_field_len
    replace h_perform := converts_skip hcValue h_perform
    apply convertsM_bind_and hcValue
    clear hcValue
    generalize (checkDelimiterThenSubstring h_value_len_lt field.data fieldHash value colon_index
        (':'.toNat : ZMod bn254) value_index perform_result).getState sCheck5 = sValue at *
    exact checkLastCharDelimiter_convertsM h_field_val h_field_len h_perform h_maxKV_bn254
  · -- `step`'s own `convertsM_bind` leaves this goal's constraint slot as `True → …` (the
    -- contravariant threading through the `not skipChecks` step, already applied to the goal
    -- before `constraints1` was supplied above); strip it before unfolding.
    simp only [true_implies]
    unfold parses
    have h1val : (1 : ZMod bn254).val = 1 := ZMod.val_one bn254
    have hp_iff : ((!skipChecks_val) = true) ↔ ¬skipChecks_val := by cases skipChecks_val <;> simp
    constructor
    · rintro ⟨⟨hoA, hoB, hoC⟩, hChashP,
        ⟨⟨-, hD⟩, ⟨hByteN, hw1b, hw1c, hw1d⟩, hE⟩,
        ⟨hCk5Bound, hF⟩,
        ⟨⟨hCiBound, hG⟩, ⟨hByteV, hw2b, hw2c, hw2d⟩, hIacc⟩,
        ⟨hCk8Bound, hJ⟩⟩
      have heq1 : ((1 : ZMod bn254) + name_len).val = 1 + name_len.val := by
        have h := isSubstring.val_add_of_lt_val (a := (1 : ZMod bn254)) (b := name_len) (by
          rw [h1val]; exact hw1d)
        rw [h1val] at h; exact h
      have h0ltName : 0 < name_len.val := by
        have h2 := hw1d; rw [heq1, h1val] at h2; omega
      have hNameBound : name_len.val + 1 < maxKVPairLen := by
        have h3 := hCk5Bound
        rw [show (name_len + 1 : ZMod bn254) = (1 : ZMod bn254) + name_len by ring, heq1] at h3
        omega
      have heq2 : (value_index_val + value_len).val = value_index_val.val + value_len.val :=
        isSubstring.val_add_of_lt_val hw2d
      have h0ltValue : 0 < value_len.val := by
        have h4 := hw2d; rw [heq2] at h4; omega
      refine ⟨hChashP, hByteN, hByteV, hNameBound, hCiBound, hCk8Bound, h0ltName, hw2b, hw2c, hw2d,
        h0ltValue, ?_⟩
      intro fieldHash hns
      have hp := hp_iff.mpr hns
      exact ⟨hoA hp, hoB hp, hoC hp, hD hp, hE hp, hF hp, hG hp, hIacc hp, hJ hp⟩
    · rintro ⟨hChashT, hByteNT, hByteVT, hNameBoundT, hCiBoundT, hCk8BoundT, h0ltNameT, hw2bT,
        hw2cT, hw2dT, h0ltValueT, hParsesT⟩
      have h1953 : (1953 : ℕ) < bn254 := by decide
      have h0maxKV : 0 < maxKVPairLen := by omega
      have h1ltMaxKV : 1 < maxKVPairLen := by omega
      have heq1 : ((1 : ZMod bn254) + name_len).val = 1 + name_len.val :=
        ZMod.val_add_of_lt (by rw [h1val]; omega)
      have hw1b : ((1 : ZMod bn254) + name_len).val < 2 ^ minBits' maxKVPairLen := by
        rw [heq1]; have := lt_two_pow_minBits' maxKVPairLen; omega
      have hw1c : (1 : ZMod bn254).val < maxKVPairLen := by rw [h1val]; omega
      have hw1d : (1 : ZMod bn254).val < ((1 : ZMod bn254) + name_len).val := by
        rw [h1val, heq1]; omega
      have heqName1 : (name_len + 1 : ZMod bn254).val = name_len.val + 1 := by
        rw [add_comm name_len 1, heq1]; omega
      refine ⟨⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩, hChashT,
        ⟨⟨h0maxKV, fun hp => ?_⟩, ⟨hByteNT, hw1b, hw1c, hw1d⟩, fun hp => ?_⟩,
        ⟨by rw [heqName1]; exact hNameBoundT, fun hp => ?_⟩,
        ⟨⟨hCiBoundT, fun hp => ?_⟩, ⟨hByteVT, hw2bT, hw2cT, hw2dT⟩, fun hp => ?_⟩,
        ⟨hCk8BoundT, fun hp => ?_⟩⟩
      · exact (hParsesT (hp_iff.mp hp)).1
      · exact (hParsesT (hp_iff.mp hp)).2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.2.2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.2.2.2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.2.2.2.2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.2.2.2.2.2.1
      · exact (hParsesT (hp_iff.mp hp)).2.2.2.2.2.2.2.2


/-! `isSubstring.sound` takes `strHash` as a value fixed independently of `H` — as its own
docstring (above `isSubstring`'s definition, in `FString/isSubstring.lean`) says, binding `str`
this way is the caller's job. `parseJWTFieldSharedLogic` instead hashes `field` itself once and
passes that hash as `strHash` to both its name- and value-checks, so it cannot cite
`isSubstring.sound` directly: the challenge then depends on `H` through *two* hashed vectors
(`field` and the substring), not one, so the collision term doubles, `50 = 2 · 25`, one `25` per
hashed vector via `HashToField.challenge_mem_transcript_le` (the same accounting
`assertIsConcatenation.prob_challenge_root_le` already does for its three hashed strings). The
three lemmas below are the `strHash`-is-itself-hashed analogues of `isSubstring.prob_challenge_root_le`,
`isSubstring.prob_accepts_le` and `isSubstring.sound`, specific to this gadget since it is
currently their only caller. -/

/--
Soundness of `parseJWTFieldSharedLogic`. When the name or the value is not really where it is
claimed to be, `parses` holds with probability at most `(nF - 1) + (max nN nV - 1) + 50` over
`bn254`: each branch of `h_bad` reduces `parses` to one `isSubstring.accepts` conjunct (both
share `field`'s hash as their `strHash`, so `sound_hashedStr` above, not `isSubstring.sound`,
is what applies), costing `50` rather than `25` since the challenge then
depends on `H` through two hashed vectors (`field` and the substring), not one.
-/
theorem sound {nF nN nV} (field name value : String)
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
        colonIndex
        valueIndex
        } ≤ (((nF - 1) + (max nN nV - 1) + 50 : ℕ) : ENNReal) / bn254
:= by
  rcases h_bad with h_bad | h_bad
  · -- the name is not really there: reduce `parses` to the name `isSubstring.accepts` conjunct
    have h_sub : {f |
          parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
            (encodeV nN name) name.length (encodeV nV value) value.length colonIndex
            valueIndex} ⊆
        {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
          (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field) field.length)
          (encodeV nN name) name.length 1 = true} := by
      intro f hf
      unfold parses at hf
      obtain ⟨-, -, -, -, h_name, -, -, h_value, -⟩ := hf (by decide)
      exact h_name
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    have h_ns := sound_hashedStr (s := 1) field.length h_fieldLen h_nameLen
      h_namePos h_nF_name h_nm_name h_fieldBytes h_nameBytes h_bad
    simp only [Nat.cast_one] at h_ns
    refine h_ns.trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast (show nF - 1 + (nN - 1) + 50 ≤ nF - 1 + (max nN nV - 1) + 50 by omega)
  · -- the value is not really there: same, via the value conjunct, with `s := valueIndex.val`
    have h_sub : {f |
          parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
            (encodeV nN name) name.length (encodeV nV value) value.length colonIndex
            valueIndex} ⊆
        {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
          (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field) field.length)
          (encodeV nV value) value.length valueIndex = true} := by
      intro f hf
      unfold parses at hf
      obtain ⟨-, -, -, -, h_name, -, -, h_value, -⟩ := hf (by decide)
      exact h_value
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    have h_vs := sound_hashedStr (s := valueIndex.val) field.length h_fieldLen
      h_valueLen h_valuePos h_valueIndex h_nm_value h_fieldBytes h_valueBytes h_bad
    rw [ZMod.natCast_rightInverse valueIndex] at h_vs
    refine h_vs.trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast (show nF - 1 + (nV - 1) + 50 ≤ nF - 1 + (max nN nV - 1) + 50 by omega)

/--
Completeness of `parseJWTFieldSharedLogic`. When `field` really is `"` + `name` + `"` + ⟨anything⟩
+ `:` (at `colonIndex`) + ⟨anything⟩ + `value` (at `valueIndex`) + ⟨`,` or `}`⟩ — in particular,
`colonIndex`/`valueIndex` need not be adjacent to the name's closing quote or to each other, so
arbitrary bytes (e.g. whitespace, as real JSON permits between tokens) may sit in either gap —
`¬ parses` holds with probability at most `2 * (nF - 1) + 100` over `bn254`. Two differences from
`sound`'s accounting:

- Both of `parses`'s random-oracle conjuncts here are the *name* and *value* `isSubstring.accepts`
  checks, each against `field`'s self-hash as `strHash` — same shape as `sound`, so each pays `50`
  rather than `25` (`sound_hashedStr`'s docstring above explains the doubling). `complete_hashedStr`
  is the corresponding completeness fact, mirroring `isSubstring.complete` the way `sound_hashedStr`
  mirrors `isSubstring.sound`, built from `prob_rejects_le_hashedStr` instead of
  `prob_accepts_le_hashedStr`.
- `sound` only has to falsify *one* of the two checks (`h_bad` is an `∨`), so it only ever pays
  that `50` once. `complete` needs *both* checks to succeed, so `¬ parses` is a *union* of two
  failure events (either check can independently reject), not a choice between them — a
  `measure_union_le`, not a case split — so the cost is paid twice: `((nF - 1) + 50)` for each of
  the name and value checks, summing to `2 * (nF - 1) + 100`.

The other seven conjuncts of `parses` (index ordering, and the literal quote/colon/comma/brace
bytes) don't depend on the random oracle at all, and are made unconditionally true here by the
hypotheses below — stated as directly as `parses` itself needs them, not derived from assuming
any particular layout of what sits between the name, the colon, and the value. -/
theorem complete {nF nN nV} (field name value : String)
  (colonIndex valueIndex : ZMod bn254)
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
  -- `colonIndex`/`valueIndex` need only be ordered past the name/colon, and the colon must
  -- actually be there — nothing pins them to any fixed offset, so whatever (if anything) sits
  -- between the name's closing quote and the colon, or between the colon and the value, is free.
  (h_colon_order : name.length < colonIndex.val)
  (h_value_order : colonIndex.val < valueIndex.val)
  (h_open_quote : field.toList[0]? = some '\"')
  (h_close_quote : field.toList[name.length + 1]? = some '\"')
  (h_colon : field.toList[colonIndex.val]? = some ':')
  (h_last_char : field.toList[field.length - 1]? = some ',' ∨
    field.toList[field.length - 1]? = some '}') :
  randomOracle.toOuterMeasure
    {f |
      ¬parses (skipChecks_val := false) (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        colonIndex
        valueIndex
    }
      ≤ ((2 * (nF - 1) + 100 : ℕ) : ENNReal) / bn254
:= by
  -- bounds, all purely from the ordering/fit hypotheses above
  have hcolon_fl : colonIndex.val < field.length := by omega
  have hname1_fl : name.length + 1 < field.length := by omega
  have hnN_lt : nN < bn254 := by omega
  have hname_lt : name.length < bn254 := by omega
  have hvalue_lt : value.length < bn254 := by omega
  have hfield_lt : field.length < bn254 := by omega
  have hsum_lt : name.length + value.length < bn254 := by omega
  have h_name_len_val : (name.length : ZMod bn254).val = name.length :=
    ZMod.val_natCast_of_lt hname_lt
  have h_field_len_val : (field.length : ZMod bn254).val = field.length :=
    ZMod.val_natCast_of_lt hfield_lt
  have h_sum_val : ((name.length : ZMod bn254) + (value.length : ZMod bn254)).val =
      name.length + value.length := by
    rw [← Nat.cast_add]; exact ZMod.val_natCast_of_lt hsum_lt
  have h_name1_val : ((name.length : ZMod bn254) + 1).val = name.length + 1 := by
    have heq : ((name.length : ZMod bn254) + 1) = ((name.length + 1 : ℕ) : ZMod bn254) := by
      push_cast; ring
    rw [heq]
    exact ZMod.val_natCast_of_lt (by omega)
  have h_fieldM1_val : ((field.length : ZMod bn254) - 1).val = field.length - 1 := by
    have heq : (field.length : ZMod bn254) - 1 = ((field.length - 1 : ℕ) : ZMod bn254) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [heq]
    exact ZMod.val_natCast_of_lt (by omega)
  -- the seven non-oracle conjuncts of `parses`, all independent of `f`
  have hord1 : (name.length : ZMod bn254).val < colonIndex.val := by rw [h_name_len_val]; omega
  have hord2 : colonIndex.val < valueIndex.val := h_value_order
  have hord3 : (field.length : ZMod bn254).val >
      ((name.length : ZMod bn254) + (value.length : ZMod bn254)).val := by
    rw [h_field_len_val, h_sum_val]; omega
  have hw0 : (0 : ℕ) < nF := by omega
  have hw1 : (name.length + 1 : ℕ) < nF := by omega
  have hw2 : colonIndex.val < nF := by omega
  have hw3 : field.length - 1 < nF := by omega
  have hs0 : (0 : ℕ) < field.toList.length := by rw [String.length_toList]; omega
  have hs1 : (name.length + 1 : ℕ) < field.toList.length := by rw [String.length_toList]; omega
  have hs2 : colonIndex.val < field.toList.length := by rw [String.length_toList]; omega
  have hs3 : field.length - 1 < field.toList.length := by rw [String.length_toList]; omega
  have hb0 : (encodeV (p := bn254) nF field).getD 0 0 = 34 := by
    rw [encodeV_getD_of_lt hw0 hs0, List.getD_eq_getElem?_getD, h_open_quote]; decide
  have hb1 : (encodeV (p := bn254) nF field).getD (name.length + 1) 0 = 34 := by
    rw [encodeV_getD_of_lt hw1 hs1, List.getD_eq_getElem?_getD, h_close_quote]; decide
  have hb2 : (encodeV (p := bn254) nF field).getD colonIndex.val 0 = 58 := by
    rw [encodeV_getD_of_lt hw2 hs2, List.getD_eq_getElem?_getD, h_colon]; decide
  have hb3 : (encodeV (p := bn254) nF field).getD (field.length - 1) 0 = 44 ∨
      (encodeV (p := bn254) nF field).getD (field.length - 1) 0 = 125 := by
    rcases h_last_char with h | h
    · left; rw [encodeV_getD_of_lt hw3 hs3, List.getD_eq_getElem?_getD, h]; decide
    · right; rw [encodeV_getD_of_lt hw3 hs3, List.getD_eq_getElem?_getD, h]; decide
  have hb1' : (encodeV (p := bn254) nF field).getD ((name.length : ZMod bn254) + 1).val 0 = 34 := by
    rw [h_name1_val]; exact hb1
  have hb3' : (encodeV (p := bn254) nF field).getD ((field.length : ZMod bn254) - 1).val 0 = 44 ∨
      (encodeV (p := bn254) nF field).getD ((field.length : ZMod bn254) - 1).val 0 = 125 := by
    rw [h_fieldM1_val]; exact hb3
  -- `parses` reduces to exactly the two `isSubstring.accepts` conjuncts, given the above.
  -- (`apply hf` / plain `intro`, not `rintro`-style destructuring, so the `let fieldHash := …`
  -- in `parses`'s body zeta-reduces the same way `sound`'s `hf (by decide)` application does,
  -- instead of being consumed as an extra binder.)
  have hsub : {f : Query → ZMod bn254 |
      ¬parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex} ⊆
      {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field) field.length)
             (encodeV nN name) name.length 1 = false} ∪
      {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field) field.length)
             (encodeV nV value) value.length valueIndex = false} := by
    intro f hf
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    have hA : isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
        (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field) field.length)
        (encodeV nN name) name.length 1 = true := by simpa using hcon.1
    have hB : isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
        (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field) field.length)
        (encodeV nV value) value.length valueIndex = true := by simpa using hcon.2
    apply hf
    intro _
    exact ⟨hord1, hord2, hord3, hb0, hA, hb1', hb2, hB, hb3'⟩
  have hname := complete_hashedStr (s := 1) field.length h_fieldLen h_nameLen h_namePos h_nm_name
    h_fieldBytes h_nameBytes h_fit_name h_pre_name
  have hvalue := complete_hashedStr (s := valueIndex.val) field.length h_fieldLen h_valueLen
    h_valuePos h_nm_value h_fieldBytes h_valueBytes h_fit_val h_pre_val
  simp only [Nat.cast_one] at hname
  rw [ZMod.natCast_rightInverse valueIndex] at hvalue
  calc randomOracle.toOuterMeasure
        {f | ¬parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
          (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex}
      ≤ randomOracle.toOuterMeasure
          ({f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
                  (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field)
                    field.length) (encodeV nN name) name.length 1 = false} ∪
            {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
                  (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field)
                    field.length) (encodeV nV value) value.length valueIndex = false}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ randomOracle.toOuterMeasure
          {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
                  (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field)
                    field.length) (encodeV nN name) name.length 1 = false} +
        randomOracle.toOuterMeasure
          {f | isSubstring.accepts (Query.toHashFn f) (encodeV nF field)
                  (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV nF field)
                    field.length) (encodeV nV value) value.length valueIndex = false} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ (((nF - 1) + 50 : ℕ) : ENNReal) / bn254 + (((nF - 1) + 50 : ℕ) : ENNReal) / bn254 :=
        add_le_add hname hvalue
    _ = ((2 * (nF - 1) + 100 : ℕ) : ENNReal) / bn254 := by
        rw [ENNReal.div_add_div_same]
        push_cast
        ring_nf


end parseJWTFieldSharedLogic
