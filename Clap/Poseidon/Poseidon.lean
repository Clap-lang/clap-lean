import Clap.Model.HashCons.HashConsM
import Clap.Poseidon.Constants.Tables
import Clap.Model.HashCons.Eval
import Clap.Model.Monad
import Clap.Model.Convert.Specialised

namespace Clap

open HashConsM

variable {p : ℕ}

def sigma (x : BoundRef p) : ClapM p ExprRef := do
  let x2 : BoundRef p ← share (←x * x)
  let x4 ← share (←x2 * x2)
  x4 * x

def ark
  {t c : ℕ}
  (state : Vector (BoundRef p) t)
  (C : Vector (BoundRef p) c)
  (r : ℕ)
: ClapM p (Vector (BoundRef p) t) :=
  state.mapIdxM (fun i s ↦ s + C[i + r]!)

def _root_.Vector.zipWithM.{u, v, w, x}
  {n : ℕ} {α : Type u} {β : Type v} {φ : Type w} {m : Type w → Type x} [Monad m]
  (f : α → β → m φ)
  (xs : Vector α n)
  (ys : Vector β n)
: m (Vector φ n) := do
  match h: n with
  | 0 => return h▸ #v[]
  | tail_length+1 =>
    have : NeZero n := by constructor; omega
    let x := xs.head
    let y := ys.head
    let z ← f x y
    let zs ← xs.tail.zipWithM f ys.tail
    return Vector.mk ⟨z :: zs.toList⟩ (by grind)

def mix {t : ℕ}
  (state : Vector (BoundRef p) t)
  (M : Vector (Vector (BoundRef p) t) t)
: ClapM p (Vector (BoundRef p) t) :=
  state.mapIdxM (fun (i : ℕ) _ ↦ do
    let x ← state.zipWithM (fun (sj : BoundRef p) (row : Vector (BoundRef p) t) ↦ row[i]! * sj) M
    x.foldrM (λ x y => x + y) (←liftM (mkConstant 0))
  )

def mixLast {t : ℕ}
  (state : Vector (BoundRef p) t)
  (M : Vector (Vector (BoundRef p) t) t)
  (s : ℕ)
: ClapM p (BoundRef p) := do
  let x ← (state.zipWithM (fun (sj : (BoundRef p)) (row : Vector (BoundRef p) t) ↦ row[s]! * sj) M)
  x.foldrM (λ x y => mkAdd x y) (←liftM (mkConstant 0))

/--
Built with `mapIdxM` over `state` rather than as `#[out₀] ++ tail`, so the result has width
`t` by construction. The old shape needed `1 + (t - 1) = t`, i.e. `t ≠ 0`, which is not
available here. Effect order is unchanged: element 0 first, then 1 … t-1 in order.
-/
def mixS {t s : ℕ}
  (r : ℕ)
  (state : Vector (BoundRef p) t)
  (S : Vector (BoundRef p) s)
: ClapM p (Vector (BoundRef p) t) := do
  let base : ℕ := (2 * t - 1) * r
  state.mapIdxM (fun i _ ↦ if i = 0 then dotProduct base else tailAt base i)
where
  /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
  dotProduct (base : ℕ) : ClapM p (BoundRef p) := do
    -- `ofFn` rather than `S.extract base (base + t)`: the latter has width
    -- `min (base + t) s - base`, which is `t` only under `base + t ≤ s`. Indexing agrees
    -- with `extract` on that range, and `!` matches how the rest of this file reads `S`.
    let s' : Vector (BoundRef p) t := Vector.ofFn (fun i : Fin t ↦ S[base + i.val]!)
    (←state.zipWithM (· * ·) s').foldrM (λ x y => mkAdd x y) (←liftM (mkConstant 0))
  /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` for `i ∈ [1, t)` -/
  tailAt (base i : ℕ) : ClapM p (BoundRef p) := do
    mkAdd state[i]! (←state[0]! * S[base + t + i - 1]!)

def poseidonEx {n c s : ℕ}
  (inputs : Vector (BoundRef p) n)
  (initState : (BoundRef p))
  (C : Vector (BoundRef p) c)
  (S : Vector (BoundRef p) s)
  (M P : Vector (Vector (BoundRef p) (1+n)) (1+n))
: ClapM p (BoundRef p) := do
  -- Poseidon parameters (from circomlib's PoseidonEx template)
  -- N_ROUNDS_P[t-2] for t ∈ [2, 17]
  let N_ROUNDS_P : List ℕ := [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
  let t : ℕ := 1 + n
  let nRoundsF : ℕ := 8
  let nRoundsP : ℕ := N_ROUNDS_P[t - 2]!
  let half : ℕ := nRoundsF / 2

  let state : Vector ExprRef t := Vector.append #v[initState] inputs

  -- initial state: [initState, inputs[0], …, inputs[nInputs−1]]
  let state ← ark state C 0

  -- Phase 1: first-half full rounds (r = 0 … half−2), mix with M
  let state ← (List.range (half - 1)).foldlM (fun state r ↦ do
    let l ← state.mapM sigma
    mix (←ark l C ((r + 1) * t)) M) state

  -- Boundary round (r = half−1): sigma → ark → mix with P
  let state ← mix (←ark (← state.mapM sigma) C (half * t)) P

  -- Phase 2: partial rounds
  let state ← (List.range nRoundsP).foldlM (fun state r ↦ do
    let s0 ← mkAdd (← sigma state[0]!) C[(half + 1) * t + r]!
    mixS r (state.set 0 s0) S) state

  -- Phase 3: second-half full rounds (r = 0 … half−2), mix with M
  let state ← (List.range (half - 1)).foldlM (fun state r ↦ do
    let l ← state.mapM sigma
    mix (←ark l C ((half + 1) * t + nRoundsP + r * t)) M) state

  -- Final round: sigma on all, then extract nOuts elements via MixLast
  let state ← state.mapM sigma
  mixLast state M 0

def poseidon {n c s}
  (inputs : Vector ExprRef n)
  (C : Vector ExprRef c)
  (S : Vector ExprRef s)
  (M P : Vector (Vector ExprRef (1+n)) (1+n))
: ClapM p ExprRef := do
  poseidonEx inputs (←liftM (mkConstant 0)) C S M P

def allocateVector {n} (values : Vector (ZMod p) n) : ClapM p (Vector ExprRef n) := do
  values.mapM (liftM ∘ mkConstant)

def poseidonBN254 {n} (inputs : Vector ExprRef n) : ClapM Primes.bn254 ExprRef := do
  let t := 1 + n -- element 2 is at list index 0 and so on
  let C ← allocateVector (Clap.Poseidon.Constant.C t)
  let S ← allocateVector (Clap.Poseidon.Constant.S t)
  let M ← (Clap.Poseidon.Constant.M t).mapM allocateVector
  let P ← (Clap.Poseidon.Constant.P t).mapM allocateVector
  poseidon inputs C S M P

section examples

private def testp : ClapM Primes.bn254 (HashConsSt Primes.bn254 × ExprRef) := do
  let x ← liftM (mkConstant (p := Primes.bn254) 1)
  let y ← liftM (mkConstant (p := Primes.bn254) 2)
  let z ← poseidonBN254 #v[x, y]
  let σ ← getThe (HashConsSt Primes.bn254)
  return (σ, z)

/--
circomlib test vector: hash([1, 2]) with t=3
https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L50
-/
example :
  letI Γ := testp.getVarStore {} 0 {}
  letI σXz := testp.run 0 {}
  letI := σXz.1
  letI := this.1
  letI := this.1
  [Γ, this.1|this.2] =
  .some 7853200120776062878684798364095072458815029376092732009249414926327459813530 := by
  native_decide

private def testp₁ : ClapM Primes.bn254 (HashConsSt Primes.bn254 × ExprRef) := do
  let x ← liftM (mkConstant (p := Primes.bn254) 3)
  let y ← liftM (mkConstant (p := Primes.bn254) 4)
  let z ← poseidonBN254 #v[x, y]
  let σ ← getThe (HashConsSt Primes.bn254)
  return (σ, z)

/--
circomlib test vector: hash([3, 4]) with t=3
https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L60
-/
example :
  letI Γ := testp₁.getVarStore {} 0 {}
  letI σXz := testp₁.run 0 {}
  letI := σXz.1
  letI := this.1
  letI := this.1
  [Γ, this.1|this.2] =
  some 14763215145315200506921711489642608356394854266165572616578112107564877678998 := by
  native_decide

/-! More arities, from the old model's commented-out suite (`old/Clap/Poseidon/Poseidon.lean`).
`Clap.HashToField` assumes `poseidonBN254` computes *a* function at every arity from 1 to 16
(`Clap.Poseidon.Computes`); these vectors are the evidence that the circuit really is Poseidon
at the arities they cover. `Computes.evalConst_eq` carries them over to `H`: restated for
`evalConst`, each one is a value of every `H` with `Computes H`. -/

/-- `poseidonBN254` of constant inputs, evaluated in the varStore its own circuit produces. -/
private def hashOf {n : ℕ} (xs : Vector (ZMod Primes.bn254) n) : Option (ZMod Primes.bn254) :=
  let cmd : ClapM Primes.bn254 (HashConsSt Primes.bn254 × ExprRef) := do
    let refs ← xs.mapM (fun x ↦ liftM (mkConstant (p := Primes.bn254) x))
    let z ← poseidonBN254 refs
    let σ ← getThe (HashConsSt Primes.bn254)
    return (σ, z)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

/-- arity 1 (arnaucube's `poseidon-ark` suite, which `aptos_crypto::poseidon_bn254` is tested against) -/
example : hashOf #v[1] =
  some 18586133768512220936620570745912940619677854269274689475585506675881198879027 := by
  native_decide

/-- arity 4, the identity commitment's arity; also circomlibjs's `poseidonperm_x5_254_5` -/
example : hashOf #v[1, 2, 3, 4] =
  some 18821383157269793795438455681495246036402687001665670618754263018637548127333 := by
  native_decide

/-- arity 5, circomlib `test/poseidoncircuit.js#L29` -/
example : hashOf #v[1, 2, 0, 0, 0] =
  some 1018317224307729531995786483840663576608797660851238720571059489595066344487 := by
  native_decide

/-- arity 5, circomlib `test/poseidoncircuit.js#L39` -/
example : hashOf #v[3, 4, 5, 10, 23] =
  some 13034429309846638789535561449942021891039729847501137143363028890275222221409 := by
  native_decide

/-- arity 6, the nonce commitment's arity (`poseidon-ark`) -/
example : hashOf #v[1, 2, 0, 0, 0, 0] =
  some 15336558801450556532856248569924170992202208561737609669134139141992924267169 := by
  native_decide

/-- arity 6 (`poseidon-ark`) -/
example : hashOf #v[1, 2, 3, 4, 5, 6] =
  some 20400040500897583745843009878988256314335038853985262692600694741116813247201 := by
  native_decide

/-
Arities 7 to 16 are left as comments: the widest take ~45 s each, 7 to 15 together over 10
minutes, and they would dominate the build. Keyless hashes at 12 (the RSA modulus, the `uid`
value), 13 (the extra field) and 14 (the public inputs), and 16 is `HashElemsToField`'s leaf.
`[1..n]` for `n` from 7 to 16 was checked with `native_decide` on 2026-09-24 against circomlibjs
0.1.7 (`buildPoseidon`), which also reproduces every vector above; `[1..16]` was first checked
by hand on 2026-09-23 with `#eval! hashOf …`. The two zero-padded vectors match circomlibjs but
have not been run through the circuit.

-- arities 7 to 13 and 15 (circomlibjs)
example : hashOf #v[1, 2, 3, 4, 5, 6, 7] =
  some 12748163991115452309045839028154629052133952896122405799815156419278439301912
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8] =
  some 18604317144381847857886385684060986177838410221561136253933256952257712543953
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9] =
  some 13589767895268936107593642967621470491511464502761040466226072462545218539640
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
  some 3657500514307717306974218405144578736633140001277925127187636780142269815841
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
  some 3572015662710076994097916907865950486270383304442561406230608893458731714472
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
  some 2501997477381648492950318384533644783248002172679259592360114615426357826485
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] =
  some 7041832639553862712666971417715061873827921493498355005117622707743491651590
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
  some 4203130618016961831408770638653325366880478848856764494148034853759773445968
-- arity 14 (`poseidon-ark`)
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] =
  some 8354478399926161176778659061636406690034081872658507739535256090879947077494
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0] =
  some 5540388656744764564518487011617040650780060800286365721923524861648744699539
-- arity 16 (`poseidon-ark`)
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] =
  some 9989051620750914585850546081941653841776809718687451684622678807385399211877
example : hashOf #v[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0] =
  some 11882816200654282475720830292386643970958445617880627439994635298904836126497
-/

end examples

end Clap
