import Clap.eDSLState.Exp
import Clap.Poseidon.Constant

namespace Clap

variable {p : ℕ}

def sigma (x : ExprRef) : HashConsM p ExprRef := do
  let x2 ← mkMul x x
  let x4 ← mkMul x2 x2
  mkMul x4 x

def ark
  {t c : ℕ}
  (state : Vector ExprRef t)
  (C : Vector ExprRef c)
  (r : ℕ)
: HashConsM p (Vector ExprRef t) :=
  state.mapIdxM (fun i s ↦ mkAdd s C[i + r]!)

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
  (state : Vector ExprRef t)
  (M : Vector (Vector ExprRef t) t)
: HashConsM p (Vector ExprRef t) :=
  state.mapIdxM (fun (i : ℕ) _ ↦ do
    let x ← state.zipWithM (fun (sj : ExprRef) (row : Vector ExprRef t) ↦ mkMul row[i]! sj) M
    x.foldrM (λ x y => mkAdd x y) (←mkConstant 0)
  )

def mixLast {t : ℕ}
  (state : Vector ExprRef t)
  (M : Vector (Vector ExprRef t) t)
  (s : ℕ)
: HashConsM p ExprRef := do
  let x ← (state.zipWithM (fun (sj : ExprRef) (row : Vector ExprRef t) ↦ mkMul row[s]! sj) M)
  x.foldrM (λ x y => mkAdd x y) (←mkConstant 0)

def mixS {t s : ℕ}
  (r : ℕ)
  (state : Vector ExprRef t)
  (S : Vector ExprRef s)
: HashConsM p (Vector ExprRef t) := do
  -- let t : ℕ := state.length
  let base : ℕ := (2 * t - 1) * r
  return ⟨#[←dotProduct base] ++ (←tail base).toArray, sorry⟩ -- t must not be 0
where
  /-- `out[0] = Σᵢ S[base + i] · in[i]` — full dot product for element 0 -/
  dotProduct (base : ℕ) : HashConsM p ExprRef := do
    let s' : Vector _ t := ⟨S.extract base (base+t) |>.toArray, sorry⟩
    (←state.zipWithM (mkMul · ·) s').foldrM (λ x y => mkAdd x y) (←mkConstant 0)
  /-- `out[i] = in[i] + in[0] · S[base + t + i − 1]` for `i ∈ [1, t)` -/
  tail (base : ℕ) : HashConsM p (Vector ExprRef (t-1)) := do
    (state.drop 1).mapIdxM (fun i sᵢ ↦ do mkAdd sᵢ (←mkMul state[0]! S[base + t + i]!))

def poseidonEx {n c s : ℕ}
  (inputs : Vector ExprRef n)
  (initState : ExprRef)
  (C : Vector ExprRef c)
  (S : Vector ExprRef s)
  (M P : Vector (Vector ExprRef (1+n)) (1+n))
: HashConsM p ExprRef := do
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
: HashConsM p ExprRef := do
  poseidonEx inputs (←mkConstant 0) C S M P

def allocateVector {n} (values : Vector (ZMod p) n) : HashConsM p (Vector ExprRef n) := do
  values.mapM mkConstant

def poseidonBN254 {n} (inputs : Vector ExprRef n) : HashConsM Primes.bn254 ExprRef := do
  let t := 1 + n -- element 2 is at list index 0 and so on
  let C ← allocateVector (Clap.Poseidon.Constant.C t)
  let S ← allocateVector (Clap.Poseidon.Constant.S t)
  let M ← (Clap.Poseidon.Constant.M t).mapM allocateVector
  let P ← (Clap.Poseidon.Constant.P t).mapM allocateVector
  poseidon inputs C S M P


def mkSigmaExpr (p : ℕ) (n : ℕ) : HashConsM p ExprRef := do
  let x ← HashConsM.saveExpr (.c 2)
  Array.range n |>.foldlM (init := x) (λ x _ => sigma x)

def evalSigma (p : ℕ) : HashConsM p (Option (ZMod p)) := do
  let x ← mkSigmaExpr p 1028
  let val ← eval {} x
  return val

section examples

private def test₁ : HashConsM Primes.bn254 (Option (ZMod Primes.bn254)) := do
  let x ← mkConstant 1
  let y ← mkConstant 2
  let z ← poseidonBN254 #v[x, y]
  eval {} z

/--
circomlib test vector: hash([1, 2]) with t=3
https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L50
-/
example :
  (StateT.run' test₁ (HashConsSt.empty Primes.bn254)).run =
  .some 7853200120776062878684798364095072458815029376092732009249414926327459813530 := by
  native_decide

private def test₂ : HashConsM Primes.bn254 (Option (ZMod Primes.bn254)) := do
  let x ← mkConstant 3
  let y ← mkConstant 4
  let z ← poseidonBN254 #v[x, y]
  eval {} z

/--
circomlib test vector: hash([3, 4]) with t=3
https://github.com/iden3/circomlib/blob/master/test/poseidoncircuit.js#L60
-/
example :
  (StateT.run' test₂ (HashConsSt.empty Primes.bn254)).run =
  some 14763215145315200506921711489642608356394854266165572616578112107564877678998 := by
  native_decide

end examples

end Clap
