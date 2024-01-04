import MyNat

namespace MyNat

def le (a b : 𝕟) := ∃ (c : 𝕟), b = a + c

instance : LE 𝕟 where
  le := le

theorem le_iff_exists_add (a b : 𝕟) : 
  a ≤ b ↔ ∃ (c : 𝕟), b = a + c := Iff.rfl

def lt (a b : 𝕟) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT 𝕟 where
  lt := lt