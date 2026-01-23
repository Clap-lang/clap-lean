namespace Clap

@[reducible]
def typ (a r : Type) : Nat → Type
  | 0     => r
  | n + 1 => a → typ a r n

@[reducible]
def curry {α β : Type} {n : Nat} (k : Vector α n → β) : typ α β n :=
  match n with
  | 0     => k #v[]
  | n + 1 => fun x => curry fun l => k ⟨⟨x :: l.toList⟩, by simp⟩

end Clap
