import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.xorScan
import Clap.Lang.Core.FB.ofBool
import Clap.Model.Convert.PaddedVector
import Batteries.Data.String.Lemmas
import Batteries.Data.ByteArray
import Clap.Lang.Data.JWT.Scaffold.stringBodies

namespace Clap.Lang

variable {p : ℕ}

/-- `leftArraySelector`'s body, with `oneHotRaw` in place of `singleOneArray`: the same
`1`s-then-`0`s prefix mask, but without the assertion that `idx < len` — `oneHotRaw` never
asserts its index is in range the way `singleOneArray` does, so this stays satisfiable (with
ideal value `1`-everywhere) even when `idx ≥ len`. -/
private def lengthMask [p.AtLeastTwo] (len : ℕ) (idx : F p) : ClapM p (FArray p len) := do
  let oneHot ← oneHotRaw len idx
  let true' ← FB.ofBool true
  oneHot.xorScan true'

/-- Given an array of ASCII characters representing a JSON object, output a binary array
demarquing the spaces in between quotes, so that the indices in between quotes in `input` are
given the value `1` in the output, and are 0 otherwise. Escaped quotes are not considered quotes
in this subcircuit (ported from `old/Clap/JWT.lean`'s `stringBodies`).

Five stages, each a field-arithmetic scan or pointwise map over 0/1 values
(`AND a b = a*b`, `NOT a = 1-a`, `XOR a b = a+b-2ab`):

1. `wasEscapedArr` — exclusive-prefix scan: was the *previous* character an active, unescaped
   backslash (`0` at position `0`, no previous character).
2. `isQuoteCharArr` — pointwise: is this character a real, unescaped `"`.
3. `openedBeforeArr` — exclusive-prefix XOR-scan of `isQuoteCharArr`: the quote-parity (are we
   inside a string?) just before this character.
4. `rawInsideQuotesArr` — pointwise: "inside quotes, and not itself a quote mark" — correct for
   real characters, but may stay `1` through the zero-padded tail if the real content ends with
   an odd number of quotes (an unterminated string).
5. `lengthMaskArr` + the final multiply — `1` for `i < input.len`, `0` from there on, so the
   zero-padded tail always reads `0` regardless of what stage 4 computed for it. Built from
   `oneHotRaw` (not `singleOneArray`/`leftArraySelector`) specifically so this stays satisfiable
   — with ideal value `1`-everywhere — even when `input.len ≥ w` (no padding at all): `oneHotRaw`
   doesn't assert its index is in range the way `singleOneArray` does. -/
def stringBodies [p.AtLeastTwo] {w} (input : FString p w) : ClapM p (FArray p w) := do
  let zeroF ← mkF 0
  -- Stage 1: wasEscapedArr[i] = "was position i-1 an active, unescaped backslash".
  let wasEscapedArr ← Vector.scanlM (fun wasEscaped char ↦ do
    let isBackslash ← eq char (← mkF 92)
    -- NOT wasEscaped: `1 - x` is boolean negation for a 0/1 field value `x`.
    let notWasEscaped ← mkSub (← mkF 1) wasEscaped
    mkMul isBackslash notWasEscaped) zeroF input.data
  -- Stage 2: isQuoteCharArr[i] = "character i is an unescaped double-quote".
  let isQuoteCharArr ← (input.data.zip wasEscapedArr).mapM (fun (char, wasEscaped) ↦ do
    let isQuoteChar ← eq char (← mkF 34)
    -- NOT wasEscaped (same 1 - x pattern as stage 1).
    let notWasEscaped ← mkSub (← mkF 1) wasEscaped
    mkMul isQuoteChar notWasEscaped)
  -- Stage 3: openedBeforeArr[i] = quote-parity (inside a string?) just before position i.
  let openedBeforeArr ← Vector.scanlM (fun openedBefore isQuoteChar ↦ do
    let product ← mkMul openedBefore isQuoteChar
    let twiceProduct ← mkAdd product product
    let sum ← mkAdd openedBefore isQuoteChar
    mkSub sum twiceProduct) zeroF isQuoteCharArr
  -- Stage 4: rawInsideQuotesArr[i] = "inside quotes, and not itself a quote mark" (unmasked).
  let rawInsideQuotesArr ← (openedBeforeArr.zip isQuoteCharArr).mapM
    (fun (openedBefore, isQuoteChar) ↦ do
      -- NOT isQuoteChar: again `1 - x` for a 0/1 field value.
      let notQuoteChar ← mkSub (← mkF 1) isQuoteChar
      mkMul openedBefore notQuoteChar)
  -- Stage 5: truncate to the string's real length, so the padded tail always reads 0.
  let lengthMaskArr ← lengthMask w input.len
  (rawInsideQuotesArr.zip lengthMaskArr).mapM (fun (raw, maskBit) ↦ mkMul raw maskBit)

namespace stringBodies

def isEscape (bs : ByteArray) (i : Fin bs.size) : Bool :=
  match _ : i.val with
  | 0 => bs[i.val] = '\\'.toUInt8
  | i' + 1 => bs[i] = '\\'.toUInt8 ∧ ¬ isEscape bs ⟨i', by lia⟩

def isQuotation (bs : ByteArray) (i : Fin bs.size) : Bool :=
  match _ : i.val with
  | 0 => bs[i] = '"'.toUInt8
  | i' + 1 => bs[i] = '"'.toUInt8 ∧ ¬ isEscape bs ⟨i', by lia⟩

def oddNrQuotesUntil (bs : ByteArray) (i : Fin bs.size) : Bool :=
  Odd {j | j ≤ i ∧ isQuotation bs j}.toFinset.card

def isInQuotes (bs : ByteArray) (i : Fin bs.size) : Bool :=
  ¬isQuotation bs i ∧ oddNrQuotesUntil bs i

def isInQuotes' (bs : ByteArray) (i : ℕ) : Bool :=
  if h : i < bs.size then
    ¬isQuotation bs ⟨i, h⟩ ∧ oddNrQuotesUntil bs ⟨i, h⟩
  else
    false

/-! ### Recurrence for `oddNrQuotesUntil`

Turns the `Finset.card`/`Odd` definition into a running-XOR recurrence over `isQuotation`, which
lines up with `openedArr`'s scan. -/

private lemma oddNrQuotesUntil_zero (bs : ByteArray) (h : 0 < bs.size) :
    oddNrQuotesUntil bs ⟨0, h⟩ = isQuotation bs ⟨0, h⟩ := by
  unfold oddNrQuotesUntil
  have hset : {j : Fin bs.size | j ≤ (⟨0,h⟩ : Fin bs.size) ∧ isQuotation bs j}
      = (if isQuotation bs ⟨0,h⟩ then {(⟨0,h⟩ : Fin bs.size)} else ∅ : Set (Fin bs.size)) := by
    ext j
    constructor
    · rintro ⟨hle, hjq⟩
      have hj0 : j = ⟨0, h⟩ := Fin.ext (by have := Fin.le_def.mp hle; simpa using this)
      subst hj0
      simp [hjq]
    · intro hmem
      by_cases hq : isQuotation bs ⟨0,h⟩ <;> simp [hq] at hmem
      subst hmem
      exact ⟨le_refl _, hq⟩
  rw [show {j : Fin bs.size | j ≤ (⟨0,h⟩ : Fin bs.size) ∧ isQuotation bs j}.toFinset.card
      = {j : Fin bs.size | j ≤ (⟨0,h⟩ : Fin bs.size) ∧ isQuotation bs j}.ncard
      from (Set.ncard_eq_toFinset_card' _).symm, hset]
  by_cases hq : isQuotation bs ⟨0,h⟩
  · simp [hq]
  · simp [hq]

set_option linter.unusedSimpArgs false in
private lemma oddNrQuotesUntil_succ (bs : ByteArray) (i' : ℕ) (h : i' + 1 < bs.size) (h' : i' < bs.size) :
    oddNrQuotesUntil bs ⟨i'+1, h⟩ = xor (oddNrQuotesUntil bs ⟨i', h'⟩) (isQuotation bs ⟨i'+1, h⟩) := by
  unfold oddNrQuotesUntil
  have hset : {j : Fin bs.size | j ≤ (⟨i'+1,h⟩ : Fin bs.size) ∧ isQuotation bs j}
      = (if isQuotation bs ⟨i'+1,h⟩
        then insert (⟨i'+1,h⟩ : Fin bs.size) {j : Fin bs.size | j ≤ (⟨i',h'⟩ : Fin bs.size) ∧ isQuotation bs j}
        else {j : Fin bs.size | j ≤ (⟨i',h'⟩ : Fin bs.size) ∧ isQuotation bs j} : Set (Fin bs.size)) := by
    ext j
    simp only [Set.mem_setOf_eq]
    have hle_iff : j ≤ (⟨i'+1,h⟩ : Fin bs.size) ↔ j.val ≤ i' + 1 := Fin.le_def
    have hle_iff' : j ≤ (⟨i',h'⟩ : Fin bs.size) ↔ j.val ≤ i' := Fin.le_def
    by_cases hq : isQuotation bs ⟨i'+1,h⟩
    · simp only [hq, if_true, Set.mem_insert_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hle, hjq⟩
        rw [hle_iff] at hle
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact Or.inr ⟨hle_iff'.mpr (by omega), hjq⟩
        · exact Or.inl (Fin.ext heq)
      · rintro (heq | ⟨hle, hjq⟩)
        · subst heq; exact ⟨le_refl _, hq⟩
        · exact ⟨hle_iff.mpr (by have := hle_iff'.mp hle; omega), hjq⟩
    · simp only [hq]
      constructor
      · rintro ⟨hle, hjq⟩
        rw [hle_iff] at hle
        refine ⟨hle_iff'.mpr ?_, hjq⟩
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · omega
        · have hj : j = (⟨i'+1,h⟩ : Fin bs.size) := by ext; exact heq
          exact absurd (hj ▸ hjq) hq
      · rintro ⟨hle, hjq⟩
        exact ⟨hle_iff.mpr (by have := hle_iff'.mp hle; omega), hjq⟩
  rw [show {j : Fin bs.size | j ≤ (⟨i'+1,h⟩ : Fin bs.size) ∧ isQuotation bs j}.toFinset.card
      = {j : Fin bs.size | j ≤ (⟨i'+1,h⟩ : Fin bs.size) ∧ isQuotation bs j}.ncard
      from (Set.ncard_eq_toFinset_card' _).symm,
    show {j : Fin bs.size | j ≤ (⟨i',h'⟩ : Fin bs.size) ∧ isQuotation bs j}.toFinset.card
      = {j : Fin bs.size | j ≤ (⟨i',h'⟩ : Fin bs.size) ∧ isQuotation bs j}.ncard
      from (Set.ncard_eq_toFinset_card' _).symm,
    hset]
  by_cases hq : isQuotation bs ⟨i'+1,h⟩
  · simp only [hq, if_true]
    have hnotmem : (⟨i'+1,h⟩ : Fin bs.size) ∉ {j : Fin bs.size | j ≤ (⟨i',h'⟩ : Fin bs.size) ∧ isQuotation bs j} := by
      rintro ⟨hle, -⟩
      have := Fin.le_def.mp hle
      simp at this
    rw [Set.ncard_insert_of_notMem hnotmem]
    simp [hq, Nat.odd_add_one, ← Nat.not_odd_iff_even]
  · simp [hq]

/-! ### Ideal-value (ZMod p arithmetic) spec, shaped to match the circuit's scan/map pipeline

Each `*StepSpec`/`*Spec` pair below mirrors one stage of `stringBodies` above, one-for-one, but
in plain `ZMod p` arithmetic with no monad: `escStepSpec`/`escSpec` ↔ stage 1
(`wasEscapedArr`), `quoteStepSpec`/`quoteSpec` ↔ stage 2 (`isQuoteCharArr`),
`parityStepSpec`/`openedSpec` ↔ stage 3 (`openedBeforeArr`), `outStepSpec`/`rawOutSpec` ↔ stage 4
(`rawInsideQuotesArr`), and `maskSpec`/`finalSpec` ↔ stage 5 (the length mask and final multiply).
Keeping the shapes identical (`Vector.scanl`/`.zip`/`.map`, matching what `convertsM_scanlM`/
`convertsM_mapM` actually produce) is what lets the final composition proof's value-equality goal
reduce to little more than `unfold` + `rfl`, instead of a separate equivalence argument. -/

private def escStepSpec (acc c : ZMod p) : ZMod p := (if c == (92 : ZMod p) then 1 else 0) * (1 - acc)
private def quoteStepSpec (bs : ZMod p × ZMod p) : ZMod p := (if bs.1 == (34 : ZMod p) then 1 else 0) * (1 - bs.2)
private def parityStepSpec (acc q : ZMod p) : ZMod p := acc + q - 2 * acc * q
private def outStepSpec (bs : ZMod p × ZMod p) : ZMod p := bs.1 * (1 - bs.2)

private def escSpec {w} (vals : Vector (ZMod p) w) : Vector (ZMod p) w :=
  Vector.scanl escStepSpec 0 vals
private def quoteSpec {w} (vals : Vector (ZMod p) w) : Vector (ZMod p) w :=
  (vals.zip (escSpec vals)).map quoteStepSpec
private def openedSpec {w} (vals : Vector (ZMod p) w) : Vector (ZMod p) w :=
  Vector.scanl parityStepSpec 0 (quoteSpec vals)
private def rawOutSpec {w} (vals : Vector (ZMod p) w) : Vector (ZMod p) w :=
  (openedSpec vals |>.zip (quoteSpec vals)).map outStepSpec

/-- The length-mask: `1` at positions `< len`, `0` elsewhere, truncating `rawOutSpec` to the
string's logical length regardless of residual scan state in the zero-padded tail. -/
private def maskSpec {w} (len : ℕ) : Vector (ZMod p) w :=
  Vector.ofFn (fun i : Fin w => if i.val < len then (1 : ZMod p) else 0)

private def finalSpec {w} (vals : Vector (ZMod p) w) (len : ℕ) : Vector (ZMod p) w :=
  ((rawOutSpec vals).zip (maskSpec len)).map (fun bs => bs.1 * bs.2)

/-! ### Per-stage step lemmas

Each lemma's `do` block is the literal circuit code for one stage (see `stringBodies` above for
what each stage means); `mkSub (← mkF 1) x` throughout is boolean NOT (`1 - x`) on a 0/1 field
value, and `mkMul`/`mkAdd`/`mkSub` combinations elsewhere spell out AND/XOR the same way. -/

private lemma escStep_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {acc c : F p} {acc_val c_val : ZMod p}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_c : Converts F.conversion state c c_val)
:
  ConvertsM F.conversion
    (do
      let isBS ← eq c (← mkF 92)
      let notAcc ← mkSub (← mkF 1) acc
      mkMul isBS notAcc)
    state (escStepSpec acc_val c_val) True
:= by
  step mkF.convertsM as ninetyTwo
  step eq.convertsM h_c h_ninetyTwo as isBS
  have h_isBS_f := F.converts_of_FB_converts h_isBS
  step mkF.convertsM as one
  step mkSub.convertsM h_one h_acc as notAcc
  apply convertsM_of_convertsM (mkMul.convertsM h_isBS_f h_notAcc)
  · unfold escStepSpec; by_cases h : c_val = 92 <;> simp [h]
  · trivial

private lemma quoteStep_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {bs : F p × F p} {c_val esc_val : ZMod p}
  (h_bs : Converts FPair.conversion state bs (c_val, esc_val))
:
  ConvertsM F.conversion
    (do
      let isQ ← eq bs.1 (← mkF 34)
      let notEsc ← mkSub (← mkF 1) bs.2
      mkMul isQ notEsc)
    state (quoteStepSpec (c_val, esc_val)) True
:= by
  have h_c := FPair.converts_fst h_bs
  have h_esc := FPair.converts_snd h_bs
  step mkF.convertsM as thirtyFour
  step eq.convertsM h_c h_thirtyFour as isQ
  have h_isQ_f := F.converts_of_FB_converts h_isQ
  step mkF.convertsM as one
  step mkSub.convertsM h_one h_esc as notEsc
  apply convertsM_of_convertsM (mkMul.convertsM h_isQ_f h_notEsc)
  · unfold quoteStepSpec; by_cases h : c_val = 34 <;> simp [h]
  · trivial

private lemma parityStep_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {acc q : F p} {acc_val q_val : ZMod p}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_q : Converts F.conversion state q q_val)
:
  ConvertsM F.conversion
    (do
      let aq ← mkMul acc q
      let aq2 ← mkAdd aq aq
      let s ← mkAdd acc q
      mkSub s aq2)
    state (parityStepSpec acc_val q_val) True
:= by
  step mkMul.convertsM h_acc h_q as aq
  step mkAdd.convertsM h_aq h_aq as aq2
  step mkAdd.convertsM h_acc h_q as s
  apply convertsM_of_convertsM (mkSub.convertsM h_s h_aq2)
  · unfold parityStepSpec; ring
  · trivial

private lemma outStep_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {bs : F p × F p} {opened_val q_val : ZMod p}
  (h_bs : Converts FPair.conversion state bs (opened_val, q_val))
:
  ConvertsM F.conversion
    (do
      let notQ ← mkSub (← mkF 1) bs.2
      mkMul bs.1 notQ)
    state (outStepSpec (opened_val, q_val)) True
:= by
  have h_opened := FPair.converts_fst h_bs
  have h_q := FPair.converts_snd h_bs
  step mkF.convertsM as one
  step mkSub.convertsM h_one h_q as notQ
  apply convertsM_of_convertsM (mkMul.convertsM h_opened h_notQ)
  · rfl
  · trivial

/-- Stage 5's step, as one composite action: `oneHotRaw` (unchecked one-hot array) followed by
`xorScan`, computing the same `1`s-then-`0`s mask `leftArraySelector` would, but with constraint
`True` throughout — `oneHotRaw` never asserts `idx < len` the way `singleOneArray` does, and
neither does `xorScan`. -/
private lemma lengthMask_convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F p}
  {state : ClapMState p}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (lengthMask len idx) state
    (Vector.ofFn (fun i : Fin len => decide (i.val < idx_val.val)))
    True
:= by
  unfold lengthMask
  step oneHotRaw.convertsM h_idx h_len as oneHot
  step (FB.ofBool.convertsM (state := oneHot_state) (b := true)) as allTrue
  apply convertsM_of_convertsM (FArray.xorScan.convertsM h_allTrue h_oneHot)
  · have htail :
        ∀ (j : ℕ) (hj : j < len),
          (scanAuxPure (Vector.ofFn (fun t : Fin len => t.val == idx_val.val)) true len (le_refl len)).tail[j]'(by omega)
            = (scanAuxPure (Vector.ofFn (fun t : Fin len => t.val == idx_val.val)) true len (le_refl len))[j + 1]'(by omega) := by
      intro j hj
      simp [Nat.add_comm]
    ext i hi
    simp only [Vector.getElem_cast, Vector.getElem_ofFn]
    rw [htail i hi]
    rw [scanAuxPure_getElem_uncond (len := len) (a := idx_val.val) len (le_refl len) (i + 1) (by omega)]
    by_cases h : idx_val.val < i + 1
    . have h' : ¬ (i < idx_val.val) := by omega
      simp [h, h']
    . have h' : i < idx_val.val := by omega
      simp [h, h']
  · trivial

/-! ### Bridging the circuit's scan/map pipeline to `isEscape`/`isQuotation`/`isInQuotes`

`escBefore`/`openedBefore` give the "state entering position `i`" reading of `isEscape`/
`oddNrQuotesUntil` that an exclusive-prefix scan naturally produces: `escBefore` is what
`wasEscapedArr` (stage 1) computes, and `openedBefore` is what `openedBeforeArr` (stage 3)
computes. `main_induction` then shows all four pre-mask stages agree with
`isEscape`/`isQuotation`/the quote-parity/`isInQuotes` at every real (non-padding) position, by
induction mirroring `isEscape`/`isQuotation`'s own recursive structure. -/

private def escBefore (bs : ByteArray) : ℕ → Bool
  | 0 => false
  | i' + 1 => if h : i' < bs.size then isEscape bs ⟨i', h⟩ else false

private def openedBefore (bs : ByteArray) : ℕ → Bool
  | 0 => false
  | i' + 1 => if h : i' < bs.size then oddNrQuotesUntil bs ⟨i', h⟩ else false

private lemma escBefore_zero (bs : ByteArray) : escBefore bs 0 = false := rfl
private lemma escBefore_succ (bs : ByteArray) (i' : ℕ) (h : i' < bs.size) :
    escBefore bs (i'+1) = isEscape bs ⟨i',h⟩ := by simp [escBefore, dif_pos h]

private lemma openedBefore_zero (bs : ByteArray) : openedBefore bs 0 = false := rfl
private lemma openedBefore_succ (bs : ByteArray) (i' : ℕ) (h : i' < bs.size) :
    openedBefore bs (i'+1) = oddNrQuotesUntil bs ⟨i',h⟩ := by simp [openedBefore, dif_pos h]

private lemma isEscape_eq_escBefore (bs : ByteArray) (i : ℕ) (h : i < bs.size) :
    isEscape bs ⟨i, h⟩ = (decide (bs[i] = '\\'.toUInt8) && !escBefore bs i) := by
  cases i with
  | zero => unfold isEscape; rw [escBefore_zero]; simp
  | succ i' =>
    have h' : i' < bs.size := by omega
    unfold isEscape
    rw [escBefore_succ bs i' h']
    simp

private lemma isQuotation_eq_escBefore (bs : ByteArray) (i : ℕ) (h : i < bs.size) :
    isQuotation bs ⟨i, h⟩ = (decide (bs[i] = '"'.toUInt8) && !escBefore bs i) := by
  cases i with
  | zero => unfold isQuotation; rw [escBefore_zero]; simp
  | succ i' =>
    have h' : i' < bs.size := by omega
    unfold isQuotation
    rw [escBefore_succ bs i' h']
    simp

private lemma oddNrQuotesUntil_eq_openedBefore (bs : ByteArray) (i : ℕ) (h : i < bs.size) :
    oddNrQuotesUntil bs ⟨i,h⟩ = xor (openedBefore bs i) (isQuotation bs ⟨i,h⟩) := by
  cases i with
  | zero => rw [openedBefore_zero]; simp; exact oddNrQuotesUntil_zero bs h
  | succ i' =>
    have h' : i' < bs.size := by omega
    rw [openedBefore_succ bs i' h']
    exact oddNrQuotesUntil_succ bs i' h h'

private lemma isInQuotes_eq (bs : ByteArray) (i : ℕ) (h : i < bs.size) :
    isInQuotes bs ⟨i,h⟩ = (openedBefore bs i && !isQuotation bs ⟨i,h⟩) := by
  unfold isInQuotes
  rw [show (¬isQuotation bs ⟨i,h⟩ ∧ oddNrQuotesUntil bs ⟨i,h⟩ : Bool)
      = (!isQuotation bs ⟨i,h⟩ && oddNrQuotesUntil bs ⟨i,h⟩) from by
    cases (isQuotation bs ⟨i,h⟩) <;> simp]
  rw [oddNrQuotesUntil_eq_openedBefore bs i h]
  cases (isQuotation bs ⟨i,h⟩) <;> cases (openedBefore bs i) <;> simp

private lemma main_induction {w} (bs : ByteArray) (vals : Vector (ZMod p) w) (h_p : 256 < p)
    (hvals : ∀ i (hi : i < bs.size) (hiw : i < w), vals[i]'hiw = ((bs[i]'hi).toNat : ZMod p)) :
    ∀ i (hi : i < bs.size) (hiw : i < w),
      (escSpec vals)[i]'hiw = (if escBefore bs i then (1:ZMod p) else 0) ∧
      (quoteSpec vals)[i]'hiw = (if isQuotation bs ⟨i,hi⟩ then (1:ZMod p) else 0) ∧
      (openedSpec vals)[i]'hiw = (if openedBefore bs i then (1:ZMod p) else 0) ∧
      (rawOutSpec vals)[i]'hiw = (if isInQuotes bs ⟨i,hi⟩ then (1:ZMod p) else 0) := by
  intro i
  induction i with
  | zero =>
    intro hi hiw
    have he0 : (escSpec vals)[0]'hiw = (if escBefore bs 0 then (1:ZMod p) else 0) := by
      unfold escSpec; rw [Vector.getElem_scanl, escBefore_zero]; simp
    have hq0 : (quoteSpec vals)[0]'hiw = (if isQuotation bs ⟨0,hi⟩ then (1:ZMod p) else 0) := by
      unfold quoteSpec
      rw [Vector.getElem_map, Vector.getElem_zip]
      show quoteStepSpec (vals[0], (escSpec vals)[0]) = _
      rw [he0, escBefore_zero]
      show quoteStepSpec (vals[0], (if (false:Bool) then (1:ZMod p) else 0)) = _
      unfold quoteStepSpec
      rw [mul_one_sub_ite, hvals 0 hi hiw]
      rw [isQuotation_eq_escBefore bs 0 hi, escBefore_zero, ← quoteByte_eq h_p]
    have ho0 : (openedSpec vals)[0]'hiw = (if openedBefore bs 0 then (1:ZMod p) else 0) := by
      unfold openedSpec; rw [Vector.getElem_scanl, openedBefore_zero]; simp
    have hr0 : (rawOutSpec vals)[0]'hiw = (if isInQuotes bs ⟨0,hi⟩ then (1:ZMod p) else 0) := by
      unfold rawOutSpec
      rw [Vector.getElem_map, Vector.getElem_zip]
      show outStepSpec ((openedSpec vals)[0], (quoteSpec vals)[0]) = _
      rw [ho0, hq0]
      unfold outStepSpec
      simp only
      rw [mul_one_sub_ite]
      rw [isInQuotes_eq bs 0 hi]
    exact ⟨he0, hq0, ho0, hr0⟩
  | succ i' ih =>
    intro hi hiw
    have hi' : i' < bs.size := by omega
    have hiw' : i' < w := by omega
    obtain ⟨he, hq, ho, hr⟩ := ih hi' hiw'
    have he1 : (escSpec vals)[i'+1]'hiw = (if escBefore bs (i'+1) then (1:ZMod p) else 0) := by
      unfold escSpec
      rw [getElem_scanl_succ]
      show escStepSpec ((Vector.scanl escStepSpec 0 vals)[i']'hiw') (vals[i']'hiw') = _
      have he' : (Vector.scanl escStepSpec 0 vals)[i']'hiw' = (if escBefore bs i' then (1:ZMod p) else 0) := he
      rw [he', escBefore_succ bs i' hi']
      unfold escStepSpec
      rw [mul_one_sub_ite, hvals i' hi' hiw']
      rw [isEscape_eq_escBefore bs i' hi', ← backslashByte_eq h_p]
    have hq1 : (quoteSpec vals)[i'+1]'hiw = (if isQuotation bs ⟨i'+1,hi⟩ then (1:ZMod p) else 0) := by
      unfold quoteSpec
      rw [Vector.getElem_map, Vector.getElem_zip]
      show quoteStepSpec (vals[i'+1]'hiw, (escSpec vals)[i'+1]'hiw) = _
      rw [he1, escBefore_succ bs i' hi']
      unfold quoteStepSpec
      rw [mul_one_sub_ite, hvals (i'+1) hi hiw]
      rw [isQuotation_eq_escBefore bs (i'+1) hi, escBefore_succ bs i' hi', ← quoteByte_eq h_p]
    have ho1 : (openedSpec vals)[i'+1]'hiw = (if openedBefore bs (i'+1) then (1:ZMod p) else 0) := by
      unfold openedSpec
      rw [getElem_scanl_succ]
      show parityStepSpec ((Vector.scanl parityStepSpec 0 (quoteSpec vals))[i']'hiw')
          ((quoteSpec vals)[i']'hiw') = _
      have ho' : (Vector.scanl parityStepSpec 0 (quoteSpec vals))[i']'hiw'
          = (if openedBefore bs i' then (1:ZMod p) else 0) := ho
      rw [ho', hq]
      unfold parityStepSpec
      rw [add_sub_two_mul_ite]
      rw [openedBefore_succ bs i' hi', oddNrQuotesUntil_eq_openedBefore bs i' hi']
    have hr1 : (rawOutSpec vals)[i'+1]'hiw = (if isInQuotes bs ⟨i'+1,hi⟩ then (1:ZMod p) else 0) := by
      unfold rawOutSpec
      rw [Vector.getElem_map, Vector.getElem_zip]
      show outStepSpec ((openedSpec vals)[i'+1]'hiw, (quoteSpec vals)[i'+1]'hiw) = _
      rw [ho1, hq1]
      unfold outStepSpec
      rw [mul_one_sub_ite]
      rw [isInQuotes_eq bs (i'+1) hi]
    exact ⟨he1, hq1, ho1, hr1⟩

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a : FString p k}
  {a_val : String}
  (h_a : Converts FString.conversion state a a_val)
  (h_p : 256 < p)
  (h_k : k < p)
  (h_len : a_val.length < p)
:
  ConvertsM FArray.conversion (stringBodies a) state
    (Vector.ofFn fun i ↦ isInQuotes' a_val.toAsciiByteArray i)
    True
:= by
  have h_data := FString.converts_data h_a
  have h_len_fs := FString.converts_len h_a
  have hval_len : ((a_val.length : ZMod p)).val = a_val.length :=
    ZMod.val_natCast_of_lt h_len
  -- The length mask, read off `lengthMask_convertsM`'s Bool-valued ideal, matches `maskSpec`
  -- (the field-arithmetic form `rawOutSpec`/`finalSpec` are built from).
  have h_lengthMask_eq : (Vector.ofFn (fun i : Fin k => decide (i.val < (a_val.length : ZMod p).val))).map
      (fun b => if b then (1 : ZMod p) else 0) = maskSpec (p := p) (w := k) a_val.length := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, maskSpec, hval_len, decide_eq_true_eq]
  -- Chain the five circuit stages via `step`, each fed its own per-stage step lemma; every
  -- stage (including `lengthMask_convertsM`) has constraint `True`, so `step` auto-discharges
  -- all of them.
  have h_fvec : ConvertsM FVec.conversion (stringBodies a) state
      (finalSpec (FString.encodeV k a_val) a_val.length) True := by
    unfold stringBodies
    step mkF.convertsM as zeroF
    step (convertsM_scanlM (FVec.converts_iff_F_converts.mp h_data) h_zeroF
      (fun h_acc h_c ↦ escStep_convertsM h_acc h_c)) as wasEscapedArr
    step (convertsM_mapM (C_elem := FPair.conversion) (f_spec := quoteStepSpec)
      (fun i ↦ FVec.converts_zip h_data h_wasEscapedArr i.isLt)
      (fun h_bs ↦ quoteStep_convertsM h_bs)) as isQuoteCharArr
    step (convertsM_scanlM (FVec.converts_iff_F_converts.mp h_isQuoteCharArr) h_zeroF
      (fun h_acc h_q ↦ parityStep_convertsM h_acc h_q)) as openedBeforeArr
    step (convertsM_mapM (C_elem := FPair.conversion) (f_spec := outStepSpec)
      (fun i ↦ FVec.converts_zip h_openedBeforeArr h_isQuoteCharArr i.isLt)
      (fun h_bs ↦ outStep_convertsM h_bs)) as rawInsideQuotesArr
    step (lengthMask_convertsM h_len_fs h_k) as lengthMaskArr
    apply convertsM_of_convertsM
      (convertsM_mapM (C_elem := FPair.conversion) (f_spec := fun bs => bs.1 * bs.2)
        (fun i ↦ FVec.converts_zip h_rawInsideQuotesArr
          (FVec.converts_of_FArray_converts h_lengthMaskArr) i.isLt)
        (fun h_bs ↦ by
          have h_x := FPair.converts_fst h_bs
          have h_y := FPair.converts_snd h_bs
          exact mkMul.convertsM h_x h_y))
    -- Value equality: the composed pipeline literally unfolds to `finalSpec`.
    · show (Vector.map outStepSpec _ |>.zip _ |>.map (fun bs => bs.1 * bs.2))
          = finalSpec (FString.encodeV k a_val) a_val.length
      unfold finalSpec rawOutSpec openedSpec quoteSpec escSpec
      rw [h_lengthMask_eq]
    -- Every stage's constraint is `True`, so the whole composed constraint is `True`.
    · trivial
  refine ⟨?_, h_fvec.wellFormed, h_fvec.constraints⟩
  refine converts_cast h_fvec.result ?_ ?_
  · rfl
  -- Match `finalSpec` against the `isInQuotes'` target, position by position: inside the real
  -- string (`i < a_val.length`) via `main_induction`; in the zero-padded tail, via the mask.
  congr 1
  apply Vector.ext
  intro i hi
  unfold finalSpec rawOutSpec maskSpec
  simp only [Vector.getElem_map, Vector.getElem_zip, Vector.getElem_ofFn]
  by_cases h : i < a_val.length
  · -- Real character: the mask bit is 1, so this reduces to `main_induction`'s `isInQuotes` fact.
    have h_bs : i < a_val.toAsciiByteArray.size := by rwa [toAsciiByteArray_size]
    obtain ⟨_, hq, _, hr⟩ := main_induction a_val.toAsciiByteArray (FString.encodeV k a_val) h_p
      (fun j hj hjk ↦ by
        rw [FString.encodeV_getElem_of_lt hjk (by rw [← toAsciiByteArray_size]; exact hj),
          toAsciiByteArray_getElem a_val j hj])
      i h_bs hi
    simp only [h, if_true]
    unfold isInQuotes'
    rw [dif_pos h_bs]
    unfold rawOutSpec at hr
    simp only [Vector.getElem_map, Vector.getElem_zip] at hr
    unfold isInQuotes at hr
    rw [hr, mul_one]
  · -- Zero-padded tail: the mask bit is 0, matching `isInQuotes'`'s `false` regardless of the
    -- raw (possibly nonzero) scan state there.
    have h_bs : ¬ i < a_val.toAsciiByteArray.size := by rwa [toAsciiByteArray_size]
    simp only [h, if_false, mul_zero]
    unfold isInQuotes'
    rw [dif_neg h_bs]
    rfl

end stringBodies

end Clap.Lang
