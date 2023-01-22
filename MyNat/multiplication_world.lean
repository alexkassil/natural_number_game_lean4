import MyNat
import MyNat.addition_world

open MyNat

lemma mul_zero (a : MyNat) : a * zero = zero := by rfl
lemma mul_succ (a b : MyNat) : a * succ b = a + (a * b) := by rfl

lemma zero_mul (m : MyNat) : zero * m = zero :=
  by induction m with 
  | zero => rw [mul_zero]
  | succ m' ih => rw [mul_succ, ih, zero_add]

lemma mul_one (m : MyNat) : m * 1 = m := 
  by rw [one_eq_succ_zero, mul_succ, mul_zero, add_zero]

lemma one_mul (m : MyNat) : 1 * m = m :=
  by induction m with
  | zero => rw [mul_zero]
  | succ m' ih => rw [mul_succ, ih, add_comm, succ_eq_add_one]

lemma mul_add (t a b : MyNat) : t * (a + b) = t * a + t * b :=
  by induction b with 
  | zero => rw [mul_zero, add_zero, add_zero]
  | succ b' ih => rw [add_comm, succ_add, mul_succ, add_comm b' a, ih, ←add_assoc, add_right_comm, ← mul_succ, add_comm]