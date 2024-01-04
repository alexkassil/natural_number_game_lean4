import MyNat.le
import MyNat.addition_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world
import Mathlib.Init.Order.Defs

namespace MyNat

lemma one_add_le_self (x : 𝕟) : x ≤ 1 + x := by
  exists 1
  rewrite [add_comm]
  rfl

lemma le_refl (x : 𝕟) : x ≤ x := by
  exists 0

theorem le_succ (a b : 𝕟) : a ≤ b → a ≤ succ b := by
  intro h
  cases h with
  | intro c h' => 
    exists (succ c)
    rewrite [h', add_succ]
    rfl

lemma zero_le (a : 𝕟) : 0 ≤ a := by
  induction a with
  | zero => exact le_refl zero
  | succ a' h => exact le_succ zero a' h

theorem le_trans (a b c : 𝕟) 
  (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by 
  cases hab with 
  | intro d hab' =>
  cases hbc with 
  | intro e hbc' =>
  exists (d + e)
  rewrite [←add_assoc, ←hab']
  exact hbc'
    
theorem le_antisymm (a b : 𝕟)
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

theorem le_zero (a : 𝕟) (h : a ≤ 0) : a = 0 := by
  cases h with 
  | intro _ h =>
  exact add_right_eq_zero _ _ (Eq.symm h)

theorem le_total (a b : 𝕟) : a ≤ b ∨ b ≤ a := by
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

lemma le_succ_self (a : 𝕟) : a ≤ succ a := by
  rewrite [←add_one_eq_succ, add_comm]
  exact one_add_le_self a

theorem add_le_add_right (a b : 𝕟) : 
  a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h
  intro t
  cases h with
  | intro c h => 
    exists c
    rewrite [h, add_right_comm]
    rfl

theorem le_of_succ_le_succ (a b : 𝕟) : 
  succ a ≤ succ b → a ≤ b := by
  intro h
  cases h with
  | intro c h =>
    exists c
    rewrite [succ_add] at h
    exact succ_inj b (a + c) h

theorem not_succ_le_self (a : 𝕟) : ¬ (succ a ≤ a) := by
  rewrite [succ_eq_add_one, ←add_zero a, add_assoc, zero_add]
  intro h
  cases h with
  | intro c h =>
    rewrite [add_assoc] at h
    let f := add_left_cancel a zero (1 + c) h
    rewrite [add_comm, ←succ_eq_add_one] at f
    exact zero_ne_succ c f

theorem add_le_add_left (a b t : 𝕟) 
  (h : a ≤ b) : t + a ≤ t + b := by
  cases h with
  | intro c h => 
    exists c
    rewrite [h, add_assoc]
    rfl

#check LE.le

-- a < b := a ≤ b ∧ ¬ (b ≤ a)
-- a < b := succ(a) ≤ b

lemma lt_aux_one (a b : 𝕟) : 
  a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := by
  intro h
  have h1 := h.left
  have h2 := h.right
  cases h1 with
  | intro c h1 =>
    cases c with
    | zero =>
      apply False.elim
      apply h2
      exists 0
      rewrite [add_zero] at h1
      rewrite [h1]
      rfl
    | succ c => 
      exists c
      rewrite [add_succ, ←succ_add] at h1
      exact h1

lemma lt_aux_two (a b : 𝕟) : 
  succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := by
  intro h1
  constructor
  exact le_trans a (succ a) b (le_succ_self a) h1
  intro h2
  cases h1 with 
  | intro c h1 =>
  cases h2 with
  | intro d h2 =>
  rewrite [h1] at h2
  apply zero_ne_succ (c + d)
  rewrite [succ_add, add_comm a, ←succ_add, add_comm _ a, ←add_zero a, add_assoc, add_assoc] at h2
  have h3 := add_left_cancel a _ _ h2
  rewrite [zero_add, succ_add] at h3
  exact h3  

lemma lt_iff_succ_le (a b : 𝕟) : a < b ↔ succ a ≤ b :=
   ⟨lt_aux_one a b, lt_aux_two a b⟩

instance : Preorder 𝕟 where
  le_refl := le_refl
  le_trans := le_trans

instance : PartialOrder 𝕟 where
  le_antisymm := le_antisymm