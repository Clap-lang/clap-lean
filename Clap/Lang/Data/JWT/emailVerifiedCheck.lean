import Clap.Lang.Core.FB.conditionallyAssert
import Clap.Lang.Core.FB.or
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Data.FString.isPaddedOf

namespace Clap.Lang

variable {p : ℕ}

def emailVerifiedCheck [p.AtLeastTwo]
  {MAX_UID_NAME_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN : ℕ}
  (uidName : FString p MAX_UID_NAME_LEN)
  (evName  : FString p MAX_EV_NAME_LEN)
  (evValue : FString p MAX_EV_VALUE_LEN) :
  ClapM p (FB p)
:= do
  let uidIsEmail ← uidName.isPaddedOf "email"
  FB.conditionallyAssert uidIsEmail (←evName.isPaddedOf "email_verified")
  let evValueTrue ← FB.or (←evValue.isPaddedOf "true") (←evValue.isPaddedOf "\"true\"")
  FB.conditionallyAssert uidIsEmail evValueTrue
  return uidIsEmail

namespace emailVerifiedCheck

/-- The span from `evValue.isPaddedOf "true"` to the final `return`, generalised over the
abstract `uidIsEmail` bit so that `step`'s unification does not have to see through the concrete
`conditionallyAssert` that comes before it (see docs/proving-circuits.md's failure-modes table,
"state the bind over an abstract action"). -/
private lemma tail_convertsM
  [p.AtLeastTwo]
  {MAX_EV_VALUE_LEN : ℕ}
  {state : ClapMState p}
  {evValue : FString p MAX_EV_VALUE_LEN}
  {evValue_val : String}
  {uidIsEmail : FB p}
  {uidIsEmail_val : Bool}
  (h_evValue : Converts FString.conversion state evValue evValue_val)
  (h_uidIsEmail : Converts FB.conversion state uidIsEmail uidIsEmail_val)
  (h_p : 256 < p)
  (h_evValue_w : MAX_EV_VALUE_LEN < p)
  (h_evValue_len : evValue_val.length < MAX_EV_VALUE_LEN)
  (h_evValue_chars : ∀ c ∈ evValue_val.toList, c.toNat < 256)
  (h_evValue_w_lit : 6 < MAX_EV_VALUE_LEN)   -- "\"true\"".length = 6, "true".length = 4
:
  ConvertsM FB.conversion
    (evValue.isPaddedOf "true" >>= fun t1 =>
     evValue.isPaddedOf "\"true\"" >>= fun t2 =>
     FB.or t1 t2 >>= fun evValueTrue =>
     FB.conditionallyAssert uidIsEmail evValueTrue >>= fun _ =>
     pure uidIsEmail)
    state uidIsEmail_val
    (uidIsEmail_val = true → (evValue_val = "true" ∨ evValue_val = "\"true\""))
:= by
  have h_true_len : "true".length = 4 := by decide
  have h_quoted_len : "\"true\"".length = 6 := by decide
  step (FString.isPaddedOf.convertsM_string (b := "true") h_evValue h_evValue_len (by omega)
    h_evValue_chars (by decide) h_p h_evValue_w) as t1
  step (FString.isPaddedOf.convertsM_string (b := "\"true\"") h_evValue
    h_evValue_len (by omega) h_evValue_chars (by decide) h_p h_evValue_w) as t2
  step FB.or.convertsM h_t1 h_t2 as evValueTrue
  step FB.conditionallyAssert.convertsM h_uidIsEmail h_evValueTrue as assertTrue
  apply convertsM_pure
  · exact h_uidIsEmail
  · simp only [true_implies]
    intro h1 h2
    have h3 := h1 h2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h3
    exact h3
  · simp only [true_implies]
    intro hT hp
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact hT hp

/-- The first `conditionallyAssert`, stated over an abstract preceding `action` rather than the
concrete gadget, then bound to `tail_convertsM`. Keeping `action` abstract here (instead of
inlining `FB.conditionallyAssert uidIsEmail evNameCheck` directly in `convertsM`) is the
"state the bind over an abstract action" move from docs/proving-circuits.md's failure-modes
table: `converts_skip`/`convertsM_bind_and` on a *concrete* gadget term unfold its `getResult` /
`getState` during unification and time out; on an opaque `action` they do not. -/
private lemma bind_tail_convertsM
  [p.AtLeastTwo]
  {MAX_EV_VALUE_LEN : ℕ}
  {state : ClapMState p}
  {action : ClapM p Unit}
  {C1 : Prop}
  {evValue : FString p MAX_EV_VALUE_LEN}
  {evValue_val : String}
  {uidIsEmail : FB p}
  {uidIsEmail_val : Bool}
  (h_action : ConvertsM FUnit.conversion action state () C1)
  (h_evValue : Converts FString.conversion state evValue evValue_val)
  (h_uidIsEmail : Converts FB.conversion state uidIsEmail uidIsEmail_val)
  (h_p : 256 < p)
  (h_evValue_w : MAX_EV_VALUE_LEN < p)
  (h_evValue_len : evValue_val.length < MAX_EV_VALUE_LEN)
  (h_evValue_chars : ∀ c ∈ evValue_val.toList, c.toNat < 256)
  (h_evValue_w_lit : 6 < MAX_EV_VALUE_LEN)
:
  ConvertsM FB.conversion
    (action >>= fun _ =>
      evValue.isPaddedOf "true" >>= fun t1 =>
      evValue.isPaddedOf "\"true\"" >>= fun t2 =>
      FB.or t1 t2 >>= fun evValueTrue =>
      FB.conditionallyAssert uidIsEmail evValueTrue >>= fun _ =>
      pure uidIsEmail)
    state uidIsEmail_val
    (C1 ∧ (uidIsEmail_val = true → (evValue_val = "true" ∨ evValue_val = "\"true\"")))
:=
  convertsM_bind_and h_action
    (tail_convertsM (converts_skip h_action h_evValue) (converts_skip h_action h_uidIsEmail)
      h_p h_evValue_w h_evValue_len h_evValue_chars h_evValue_w_lit)

lemma convertsM
  [p.AtLeastTwo]
  {MAX_UID_NAME_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN : ℕ}
  {state : ClapMState p}
  {uidName : FString p MAX_UID_NAME_LEN}
  {evName  : FString p MAX_EV_NAME_LEN}
  {evValue : FString p MAX_EV_VALUE_LEN}
  {uidName_val : String}
  {evName_val  : String}
  {evValue_val : String}
  (h_uidName : Converts FString.conversion state uidName uidName_val)
  (h_evName : Converts FString.conversion state evName evName_val)
  (h_evValue : Converts FString.conversion state evValue evValue_val)
  (h_p : 256 < p)
  (h_uidName_w : MAX_UID_NAME_LEN < p)
  (h_evName_w  : MAX_EV_NAME_LEN  < p)
  (h_evValue_w : MAX_EV_VALUE_LEN < p)
  (h_uidName_len : uidName_val.length < MAX_UID_NAME_LEN)
  (h_evName_len  : evName_val.length  < MAX_EV_NAME_LEN)
  (h_evValue_len : evValue_val.length < MAX_EV_VALUE_LEN)
  (h_uidName_chars : ∀ c ∈ uidName_val.toList, c.toNat < 256)
  (h_evName_chars  : ∀ c ∈ evName_val.toList,  c.toNat < 256)
  (h_evValue_chars : ∀ c ∈ evValue_val.toList, c.toNat < 256)
  (h_uidName_w_lit : 5  < MAX_UID_NAME_LEN)   -- "email".length = 5
  (h_evName_w_lit  : 14 < MAX_EV_NAME_LEN)    -- "email_verified".length = 14
  (h_evValue_w_lit : 6  < MAX_EV_VALUE_LEN)   -- "\"true\"".length = 6 ≥ "true".length = 4
:
  ConvertsM FB.conversion
    (emailVerifiedCheck uidName evName evValue)
    state
    (decide (uidName_val = "email"))
    (uidName_val = "email" →
      evName_val = "email_verified" ∧ (evValue_val = "true" ∨ evValue_val = "\"true\"")
    )
:= by
  unfold emailVerifiedCheck
  have h_email_len : "email".length = 5 := by decide
  have h_verified_len : "email_verified".length = 14 := by decide
  step (FString.isPaddedOf.convertsM_string (b := "email") h_uidName h_uidName_len (by omega)
    h_uidName_chars (by decide) h_p h_uidName_w) as uidIsEmail
  step (FString.isPaddedOf.convertsM_string (b := "email_verified")
    h_evName h_evName_len (by omega) h_evName_chars (by decide) h_p
    h_evName_w) as evNameCheck

  have h_action := FB.conditionallyAssert.convertsM h_uidIsEmail h_evNameCheck
  have h_bind := bind_tail_convertsM h_action h_evValue h_uidIsEmail
    h_p h_evValue_w h_evValue_len h_evValue_chars h_evValue_w_lit

  apply convertsM_of_convertsM h_bind
  · rfl
  · simp only [true_implies, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ hp
      exact ⟨h1 hp, h2 hp⟩
    · intro h
      exact ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩

end emailVerifiedCheck

end Clap.Lang
