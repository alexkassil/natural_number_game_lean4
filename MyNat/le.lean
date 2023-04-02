import MyNat

open MyNat

def le (a b : ℕ) := ∃ (c : ℕ), b = a + c

instance : LE ℕ where
  le := le

theorem le_iff_exists_add (a b : ℕ) : 
  a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

def lt (a b : ℕ) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT ℕ where
  lt := lt