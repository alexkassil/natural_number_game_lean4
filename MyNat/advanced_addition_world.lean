import MyNat
import MyNat.addition_world

namespace MyNat

lemma succ_inj (a b : 𝕟) : succ a = succ b → a = b := by
  intro h
  cases h
  rfl
  
lemma zero_ne_succ (a : 𝕟) : zero ≠ succ a := by
  intro h
  cases h

theorem succ_succ_inj (a b : 𝕟) (h : succ (succ a) = succ (succ b)) : a = b := by
  apply succ_inj
  apply succ_inj
  exact h

theorem succ_eq_succ_of_eq (a b : 𝕟) : 
  a = b → succ a = succ b := by
  intro h
  rewrite [h]
  rfl

theorem succ_eq_succ_iff (c d : 𝕟) :
  succ c = succ d ↔ c = d := by
  constructor 
  exact succ_inj c d
  exact succ_eq_succ_of_eq c d

theorem add_right_cancel (a t b : 𝕟) :
  a + t = b + t → a = b := by
  intro h
  induction t with 
  | zero => 
    rewrite [add_zero, add_zero] at h
    exact h
  | succ t' ih => 
    rewrite [add_succ, add_succ] at h
    let h' := (succ_inj (a + t') (b + t') h)
    apply (ih h')

theorem add_left_cancel (t a b : 𝕟) :
  t + a = t + b → a = b := by
  rewrite [add_comm, add_comm t b]
  exact add_right_cancel a t b

theorem add_right_cancel_iff (t a b : 𝕟) :
  a + t = b + t ↔ a = b := by
  constructor 
  exact add_right_cancel _ _ _
  intro h
  rewrite [h]
  rfl

lemma eq_zero_of_add_right_eq_self (a b : 𝕟) :
  a + b = a → b = 0 := by
  rewrite [←add_zero a, add_assoc, zero_add]
  intro h
  exact add_left_cancel _ _ _ h

theorem succ_ne_zero (a : 𝕟) : succ a ≠ 0 := by
  intro h
  exact zero_ne_succ a h.symm

lemma add_left_eq_zero 
  (a b : 𝕟) (H : a + b = 0) : b = 0 := by
  cases b with 
  | zero => rfl
  | succ b' => 
    rewrite [add_succ] at H
    exact False.elim (succ_ne_zero (a + b') H)

lemma add_right_eq_zero (a b : 𝕟) : 
  a + b = 0 → a = 0 := by
  rewrite [add_comm]
  exact add_left_eq_zero _ _

lemma add_one_eq_succ (d : 𝕟) : d + 1 = succ d := by
  apply Eq.symm _
  exact succ_eq_add_one _

lemma ne_succ_self (n : 𝕟) : n ≠ succ n := by
  rewrite [succ_eq_add_one, ←add_zero n, add_assoc, zero_add]
  intro h
  let f := add_left_cancel _ _ _ h
  rewrite [one_eq_succ_zero] at f
  exact zero_ne_succ zero f
  