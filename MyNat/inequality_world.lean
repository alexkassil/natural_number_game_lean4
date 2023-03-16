import MyNat.le
import MyNat.addition_world

open MyNat

lemma one_add_le_self (x : ℕ) : x ≤ 1 + x := by
  exists 1
  rewrite [add_comm]
  rfl

lemma le_refl (x : ℕ) : x ≤ x := by
  exists 0

theorem le_succ (a b : ℕ) : a ≤ b → a ≤ succ b := by
  intro h
  cases h with
  | intro c h' => 
    exists (succ c)
    rewrite [h', add_succ]
    rfl

lemma zero_le (a : ℕ) : 0 ≤ a := by
  induction a with
  | zero => exact le_refl zero
  | succ a' h => exact le_succ zero a' h

theorem le_trans (a b c : ℕ) 
  (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by 
  cases hab with 
  | intro d hab' =>
  cases hbc with 
  | intro e hbc' =>
  exists (d + e)
  rewrite [←add_assoc, ←hab']
  exact hbc'
    
