import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.bracketsMap
import Clap.Lang.Data.JWT.bracketsDepthMap
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray Primes

/-- Given the string-bodies bit mask and the raw payload field elements, mask out brackets that
    sit inside a quoted string, then compute the brackets-depth map of what remains. -/
private def unquotedBracketsDepthMap {p : ℕ} [p.AtLeastTwo] {w} (bits : FArray p w)
    (vals : FVec p w) :
  ClapM p (FVec p w)
:= do
  let inverted ← bits.mapM Lang.not
  let brackets_map ← bracketsMap vals
  let unquoted_brackets ← (inverted.zip brackets_map).mapM (fun bs ↦ mkMul bs.1 bs.2)
  bracketsDepthMap unquoted_brackets

/-- Compute JSON structural analysis from the decoded JWT payload.
    Returns the payload with its hash, string bodies, and brackets depth map. -/
def computeJSONStructure (payload : FString bn254 MAX_JWT_PAYLOAD_LEN) :
  ClapM bn254 (JSONStructure bn254)
:= do
  -- Compute payload hash
  let payloadHash ← HashToField.hashBytesToField payload
  -- JSON structural analysis on raw field elements
  let stringBodies ← stringBodies payload
  let bracketsDepthMap ← unquotedBracketsDepthMap stringBodies payload.data
  pure {payload, payloadHash, stringBodies, bracketsDepthMap}

namespace unquotedBracketsDepthMap

lemma convertsM
  {p : ℕ} [p.AtLeastTwo]
  {w}
  {state : ClapMState p}
  {vals : FVec p w}
  {bits : FArray p w}
  {bits_val : Vector Bool w}
  {vals_val : Vector (ZMod p) w}
  (h_bits : Converts FArray.conversion state bits bits_val)
  (h_vals : Converts FVec.conversion state vals vals_val)
  (h_p : 2 ^ (8 + 1) < p)
:
  ConvertsM FVec.conversion (unquotedBracketsDepthMap bits vals) state
    (Vector.ofFn fun i ↦
      bracketsDepthMap.depthIgnoringOutermostBrackets
        (Vector.ofFn fun i ↦
          if bits_val[i] then 0 else
            if vals_val[i] == '{'.toNat then 1 else
              if vals_val[i] == '}'.toNat then -1 else 0) i)
    True
:= by
  unfold unquotedBracketsDepthMap
  step (convertsM_mapM (C_elem := FB.conversion)
    (f_spec := fun b => if !b then (1 : ZMod p) else 0)
    (FArray.converts_iff_FB_converts.mp h_bits)
    (fun h_x =>
      have hm := Lang.not.convertsM h_x
      ⟨F.converts_of_FB_converts hm.result, hm.wellFormed, hm.constraints⟩)) as invR
  step (bracketsMap.convertsM h_vals h_p) as bmR
  have hUqR :
      ConvertsM FVec.conversion _ _
        (Vector.ofFn fun i : Fin w ↦
          if bits_val[i] then 0 else
            if vals_val[i] == ('{'.toNat : ZMod p) then 1 else
              if vals_val[i] == ('}'.toNat : ZMod p) then -1 else 0)
        True :=
    convertsM_of_convertsM
      (convertsM_mapM (C_elem := FPair.conversion)
        (f_spec := fun bs => bs.1 * bs.2)
        (fun i ↦ FVec.converts_zip h_invR h_bmR i.isLt)
        (fun h_bs => mkMul.convertsM (FPair.converts_fst h_bs) (FPair.converts_snd h_bs)))
      (by
        apply Vector.ext
        intro i hi
        simp only [Vector.getElem_map, Vector.getElem_zip, Vector.getElem_ofFn]
        cases hb : bits_val[i] <;> simp_all)
      Iff.rfl
  step hUqR as uqR
  apply convertsM_of_convertsM (bracketsDepthMap.convertsM h_uqR)
  · rfl
  · simp

end unquotedBracketsDepthMap

namespace computeJSONStructure

open Poseidon RandomOracle Primes

-- See `hashElemsToField.lean` / `hashBytesToField.lean`: without this, `step`'s own
-- `convertsM_bind` unification tries to `whnf` through `hashBytesToField`'s definition down to
-- `poseidonBN254`, which is a ~20 000-gate circuit and blows the recursion/heartbeat budget.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- The three-stage `bind`+`pure` composition behind `computeJSONStructure`, stated over three
fully abstract actions, known only via their `ConvertsM` facts — never through
`hashBytesToField`/`stringBodies`/`unquotedBracketsDepthMap` by name. `action3` is a free
function of `action2`'s result (matching `unquotedBracketsDepthMap stringBodies payload.data`),
generalizing the single-action `bind_*_convertsM` pattern (`assertIsAsciiDigits.bind_fold_convertsM`,
`isSubstring.bind_check_convertsM`, `assertIsConcatenation`'s `bind_final_convertsM`) to a
three-stage chain. Because `action1`/`action2`/`action3` are free variables here, nothing in this
proof is headed by a concrete gadget's definition, so the `JSONStructure.converts_intro`
application below has nothing to `whnf` through — unlike `computeJSONStructure.convertsM`'s
previous proof, which unified it against a literal 3-level-deep `hashBytesToField`/`stringBodies`/
`unquotedBracketsDepthMap` nesting and blew even a 4,000,000-heartbeat budget. Instantiating this
lemma with the concrete gadgets at the call site is a shallow, first-order match against the `do`
block written out explicitly below (`convertsM_bind` already does this kind of match cheaply
everywhere else in this codebase); it never needs to unfold what `action1`/`action2`/`action3`
get assigned to. -/
private lemma bind_convertsM
  {state : ClapMState bn254}
  {payload : FString bn254 MAX_JWT_PAYLOAD_LEN} {s : String}
  (h_payload : Converts FString.conversion state payload s)
  {action1 : ClapM bn254 (F bn254)}
  {hash_val : ZMod bn254} {C1 : Prop}
  (h_action1 : ConvertsM F.conversion action1 state hash_val C1)
  {action2 : ClapM bn254 (FArray bn254 MAX_JWT_PAYLOAD_LEN)}
  {sb_val : Vector Bool MAX_JWT_PAYLOAD_LEN} {C2 : Prop}
  (h_action2 : ConvertsM FArray.conversion action2 (action1.getState state) sb_val C2)
  {action3 : FArray bn254 MAX_JWT_PAYLOAD_LEN → ClapM bn254 (FVec bn254 MAX_JWT_PAYLOAD_LEN)}
  {bdm_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN} {C3 : Prop}
  (h_action3 :
    ConvertsM FVec.conversion
      (action3 (action2.getResult (action1.getState state).numAlloc (action1.getState state).σ))
      (action2.getState (action1.getState state)) bdm_val C3)
:
  ConvertsM JSONStructure.conversion
    (do
      let payloadHash ← action1
      let stringBodies ← action2
      let bracketsDepthMap ← action3 stringBodies
      pure ({payload, payloadHash, stringBodies, bracketsDepthMap} : JSONStructure bn254))
    state (s, hash_val, sb_val, bdm_val) (C1 ∧ C2 ∧ C3)
:= by
  have h_payload1 := converts_skip h_action1 h_payload
  have h_payload2 := converts_skip h_action2 h_payload1
  have h_hash2    := converts_skip h_action2 h_action1.result
  have h_payload3 := converts_skip h_action3 h_payload2
  have h_hash3    := converts_skip h_action3 h_hash2
  have h_sb3      := converts_skip h_action3 h_action2.result
  -- An explicit type ascription on `hComposed` gives this sub-proof a fully concrete goal from
  -- the start (exactly like proving a standalone top-level lemma) — `JSONStructure.converts_intro`
  -- only pins its implicit structure/value against a *known* goal, which is how the original
  -- concrete-gadget proof's `apply convertsM_pure; exact ...` worked. Leaving this inference to a
  -- single nested term (or to `apply`'s own goal metavariables) creates a circular dependency:
  -- `constraints1` can't be solved until the inner goal is, but the inner goal isn't posed until
  -- `constraints1` is known.
  have hComposed :
      ConvertsM JSONStructure.conversion
        (do
          let payloadHash ← action1
          let stringBodies ← action2
          let bracketsDepthMap ← action3 stringBodies
          pure ({payload, payloadHash, stringBodies, bracketsDepthMap} : JSONStructure bn254))
        state (s, hash_val, sb_val, bdm_val) (C1 ∧ C2 ∧ C3 ∧ True) := by
    refine convertsM_bind_and h_action1 ?_
    refine convertsM_bind_and h_action2 ?_
    refine convertsM_bind_and h_action3 ?_
    apply convertsM_pure
    · exact JSONStructure.converts_intro h_payload3 h_hash3 h_sb3 h_action3.result
    · trivial
  exact convertsM_of_convertsM hComposed rfl (by tauto)

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  {payload : FString bn254 MAX_JWT_PAYLOAD_LEN}
  {s : String}
  (h_payload : Converts FString.conversion state payload s)
  (h_len_s : s.length ≤ MAX_JWT_PAYLOAD_LEN) :
  let payload_vals := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN s
  ConvertsM JSONStructure.conversion (computeJSONStructure payload) state
    ⟨ s,
      HashToField.hashBytesToFieldSpec H payload_vals (s.length : ZMod bn254),
      Vector.ofFn fun i ↦ stringBodies.isInQuotes' s.toAsciiByteArray i,
      let unquoted_brackets :=
        Vector.ofFn fun i ↦
          if stringBodies.isInQuotes' s.toAsciiByteArray i then 0 else
            if payload_vals[i] == '{'.toNat then 1 else
              if payload_vals[i] == '}'.toNat then -1 else 0
      Vector.ofFn fun i ↦
        bracketsDepthMap.depthIgnoringOutermostBrackets unquoted_brackets i
    ⟩
    (∀ i : Fin MAX_JWT_PAYLOAD_LEN, payload_vals[i].val < 2 ^ 8)
:= by
  intro payload_vals
  unfold computeJSONStructure
  have h_data := FString.converts_data h_payload
  have h_len := FString.converts_len h_payload
  have h_len_bn : s.length < bn254 := lt_of_le_of_lt h_len_s (by decide)
  have hTerm1 := HashToField.hashBytesToField.convertsM h_H h_data h_len (by decide)
  have hTerm2 := stringBodies.convertsM
    (converts_skip hTerm1 h_payload) (by decide) (by decide) h_len_bn
  have hTerm3 := unquotedBracketsDepthMap.convertsM
    hTerm2.result (converts_skip hTerm2 (converts_skip hTerm1 h_data)) (by decide)
  -- `action3` is pinned explicitly: it's a higher-order implicit, and `hTerm3`'s own type only
  -- applies it at one point (`stringBodies`'s *result expression*, not a bound variable), which
  -- isn't a Miller pattern — Lean's unifier can't invert that into a lambda on its own and falls
  -- back to an expensive search instead (confirmed: without this, the call below alone exhausts
  -- 200,000 heartbeats even though `bind_convertsM`'s own proof is cheap).
  apply convertsM_of_convertsM
    (bind_convertsM (action3 := fun sb ↦ unquotedBracketsDepthMap sb payload.data)
      h_payload hTerm1 hTerm2 hTerm3)
  · simp [payload_vals]
  · simp only [payload_vals, and_true]

end computeJSONStructure
