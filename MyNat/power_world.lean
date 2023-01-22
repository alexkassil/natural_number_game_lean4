import MyNat
import MyNat.addition_world
import MyNat.multiplication_world

open MyNat

lemma pow_zero (a : MyNat) : a ^ zero = 1 := rfl
lemma pow_succ (a : MyNat) : a ^ succ b = a * (a ^ b) := rfl

lemma zero_pow_zero : (zero : MyNat) ^ zero = 1 := rfl

lemma zero_pow_succ (m : MyNat) : zero ^ (succ m) = zero :=
  by rewrite [pow_succ, zero_mul] rfl

lemma pow_one (a : MyNat) : a ^ 1 = a :=
  by rewrite [one_eq_succ_zero, pow_succ, pow_zero, mul_one] rfl

lemma pow_add (a m n : MyNat) : a ^ (m + n) = a ^ m * a ^ n :=
  by induction m with
  | zero => rewrite [zero_add, pow_zero, one_mul] rfl
  | succ m' ih => rewrite [pow_succ, succ_add, pow_succ, ih, mul_assoc] rfl