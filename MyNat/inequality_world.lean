import MyNat.le
import MyNat.addition_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

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
    
theorem le_antisem (a b : ℕ)
  (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with 
  | intro c hab => 
  cases hba with
  | intro c' hba => 
  rewrite [hab, add_assoc,]at hba
  have h1 := eq_zero_of_add_right_eq_self _ _ (Eq.symm hba)
  have h2 := add_left_eq_zero _ _ h1
  rewrite [h2, zero_equal_numeral, add_zero] at h1
  rewrite [h1, add_zero] at hab
  exact (Eq.symm hab)

theorem le_zero (a : ℕ) (h : a ≤ 0) : a = 0 := by
  cases h with 
  | intro _ h =>
  exact add_right_eq_zero _ _ (Eq.symm h)

theorem le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  induction b with
  | zero => exact (Or.inr (zero_le a))
  | succ b ih => 
  exact (
    Or.elim
    ih
    (fun a_le_b => Or.inl (le_succ _ _ a_le_b))
    (fun b_le_a => by
      rewrite [le_iff_exists_add] at b_le_a
      cases b_le_a with
      | intro c h => 
        cases c with
        | zero => 
          rewrite [add_zero] at h
          rewrite [h, succ_eq_add_one, add_comm]
          exact (Or.inl (one_add_le_self b))
        | succ c => 
          apply Or.inr
          exists c
          rewrite [add_succ, add_comm, ←add_succ, ←add_comm] at h
          trivial
    )
  )

lemma le_succ_self (a : ℕ) : a ≤ succ a := by
  rewrite [←add_one_eq_succ, add_comm]
  exact one_add_le_self a

theorem add_le_add_right (a b : ℕ) : 
  a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h
  intro t
  cases h with
  | intro c h => 
    exists c
    rewrite [h, add_right_comm]
    rfl

theorem le_of_succ_le_succ (a b : ℕ) : 
  succ a ≤ succ b → a ≤ b := by
  intro h
  cases h with
  | intro c h =>
    exists c
    rewrite [succ_add] at h
    exact succ_inj b (a + c) h

theorem not_succ_le_self (a : ℕ) : ¬ (succ a ≤ a) := by
  rewrite [succ_eq_add_one, ←add_zero a, add_assoc, zero_add]
  intro h
  cases h with
  | intro c h =>
    rewrite [add_assoc] at h
    let f := add_left_cancel a zero (1 + c) h
    rewrite [add_comm, ←succ_eq_add_one] at f
    exact zero_ne_succ c f

theorem add_le_add_left (a b t : ℕ) 
  (h : a ≤ b) : t + a ≤ t + b := by
  cases h with
  | intro c h => 
    exists c
    rewrite [h, add_assoc]
    rfl
