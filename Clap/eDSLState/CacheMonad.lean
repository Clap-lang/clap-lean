import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Exp

namespace Clap.Edsl

abbrev CacheIdx := ℕ

inductive CacheExp (p : ℕ) where
  | leaf (_ : FixedExp p)
  | add (_ _ : CacheIdx)
  | mul (_ _ : CacheIdx)
  | sub (_ _ : CacheIdx)
  deriving DecidableEq, Hashable, Inhabited, Repr

abbrev CacheM (p : ℕ) (M : Type → Type) (α : Type) : Type := WriterT (Array (CacheExp p)) M α

variable {p : ℕ} {M : Type → Type} [Monad M]

def checkExists (e : CacheExp p) : CacheM p M (Option CacheIdx) := do
  let (_, cache) : Unit × (Array (CacheExp p)) ← listen (do return ())
  let found := cache.idxOf e
  if found = cache.size then
    return .none
  else
    return .some found

def addToCache (e : CacheExp p) : CacheM p M CacheIdx := do
  let (_, cache) ← listen (do return ())
  let size := cache.size
  tell #[e]
  return size

def add (lhs rhs: CacheIdx) : CacheM p M CacheIdx := do
  -- Check whether lhs + rhs is in the cache
  let result ← checkExists (.add lhs rhs)
  -- If it isn't, add it
  match result with
    | .none => do
      addToCache (.add lhs rhs)
    | .some idx => return idx

def toValue (e : CacheIdx) (varStore : VarStore p) : CacheM p M (Option (ZMod p)) := do
  let (_, cache) ← listen (do return ())
  let map : Std.ExtTreeMap CacheIdx (Option (ZMod p)) := cache.zipIdx.foldl (λ values (elem, idx) => (
    match elem with
      | .leaf l => values.insert idx (l.eval varStore)
      | .add lhs rhs => values.insert idx ((values.get? lhs).join.bind (λ lhs: ZMod p => (
        (values.get? rhs).join.bind (λ rhs : ZMod p => lhs + rhs))
      ))
      | .sub lhs rhs => values.insert idx ((values.get? lhs).join.bind (λ lhs: ZMod p => (
        (values.get? rhs).join.bind (λ rhs : ZMod p => lhs - rhs))
      ))
      | .mul lhs rhs => values.insert idx ((values.get? lhs).join.bind (λ lhs: ZMod p => (
        (values.get? rhs).join.bind (λ rhs : ZMod p => lhs * rhs))
      ))
  )) Std.ExtTreeMap.empty
  return (map.get? e).join

def notAnExample : CacheM p Id (CacheIdx × Option (ZMod p)) := do
  let c1 ← addToCache (.leaf (Exp.c 5))
  let x ← add c1 c1
  let value ← toValue x {}
  return (x, value)

def runNotAnExample : ((CacheIdx × Option (ZMod p)) × (Array (CacheExp p))) := (WriterT.run (do
  let x ← notAnExample
  return x))

#eval runNotAnExample (p := 57)


end Clap.Edsl
