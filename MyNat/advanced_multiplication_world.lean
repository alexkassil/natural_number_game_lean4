import MyNat
import MyNat.multiplication_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

open MyNat

theorem mul_pos (a b : ℕ) : 
  a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  intro nea neb
  cases a with 
  | zero => 
    exact False.elim nea.irrefl
  | succ a' => 
    cases b with 
    | zero => exact False.elim neb.irrefl
    | succ b' => 
      rewrite [succ_mul, add_comm, succ_add]
      exact succ_ne_zero _

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : ℕ) 
  (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases a with
  | zero => 
    rewrite [zero_mul] at h
    exact Or.inl h
  | succ a' => 
    cases b with
    | zero => 
      rewrite [mul_zero] at h
      exact Or.inr h
    | succ b' => 
      let nea := succ_ne_zero a'
      let neb := succ_ne_zero b'
      let f := mul_pos (succ a') (succ b') nea neb
      exact (False.elim (Ne.elim f h))

theorem mul_eq_zero_iff (a b : ℕ) :
  a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor 
  { exact eq_zero_or_eq_zero_of_mul_eq_zero a b }
  { intro h
  exact (
    h.elim
    (fun a0 => by
      rewrite [a0, zero_equal_numeral, zero_mul]
      rfl

    )
    (fun b0 => by
      rewrite [b0, zero_equal_numeral, mul_zero]
      rfl
    )
  )
  }

theorem mul_left_cancel (a b c : ℕ) 
  (ha : a ≠ 0) : a * b = a * c → b = c := by
  intro h
  induction c generalizing b with 
  | zero => 
    rewrite [mul_zero] at h
    let f := eq_zero_or_eq_zero_of_mul_eq_zero _ _ h
    exact (
      Or.elim f
      (fun a0 => False.elim (ha.elim a0))
      id
    )
  | succ c' ih => 
    induction b with 
    | zero =>  
      rewrite [mul_zero] at h
      let f := eq_zero_or_eq_zero_of_mul_eq_zero _ _ h.symm
      exact (
        Or.elim f
        (fun a0 => False.elim (ha.elim a0))
        Eq.symm
      )
    | succ b' _ => 
      rewrite [mul_succ, mul_succ] at h
      let f := add_left_cancel _ _ _ h
      let f' := (ih b') f
      rewrite [f']
      rfl