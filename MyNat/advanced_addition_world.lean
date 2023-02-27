import MyNat
import MyNat.addition_world

open MyNat

lemma succ_inj (a b : ℕ) : succ a = succ b → a = b := by
  intro h
  cases h
  rfl
  
lemma zero_ne_succ (a : ℕ) : zero ≠ succ a := by
  intro h
  cases h

theorem succ_succ_inj (a b : ℕ) (h : succ (succ a) = succ (succ b)) : a = b := by
  apply succ_inj
  apply succ_inj
  exact h

theorem succ_eq_succ_of_eq (a b : ℕ) : 
  a = b → succ a = succ b := by
  intro h
  rewrite [h]
  rfl

theorem succ_eq_succ_iff (c d : ℕ) :
  succ c = succ d ↔ c = d := by
  constructor 
  exact succ_inj c d
  exact succ_eq_succ_of_eq c d

theorem add_right_cancel (a t b : ℕ) :
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


theorem add_left_cancel (t a b : ℕ) :
  t + a = t + b → a = b := by
  rewrite [add_comm, add_comm t b]
  exact add_right_cancel a t b