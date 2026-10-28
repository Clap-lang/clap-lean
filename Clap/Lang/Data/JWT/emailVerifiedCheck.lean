import Clap.Lang.Core.FB.conditionallyAssert
import Clap.Lang.Core.FB.or
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Data.FString.isPaddedOf
import Clap.Lang.Data.JWT.Scaffold.emailVerifiedCheck

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
