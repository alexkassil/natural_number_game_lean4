import MyNat
import MyNat.addition_world
import MyNat.multiplication_world

namespace MyNat

lemma pow_zero (a : 𝕟) : a ^ zero = 1 := rfl
lemma pow_succ (a : 𝕟) : a ^ succ b = a * (a ^ b) := rfl

lemma zero_pow_zero : (zero : 𝕟) ^ zero = 1 := rfl

lemma zero_pow_succ (m : 𝕟) : zero ^ (succ m) = zero :=
  by rewrite [pow_succ, zero_mul]; rfl

lemma pow_one (a : 𝕟) : a ^ (1 : 𝕟) = a :=
  by rewrite [one_eq_succ_zero, pow_succ, pow_zero, mul_one]; rfl

lemma pow_add (a m n : 𝕟) : a ^ (m + n) = a ^ m * a ^ n :=
  by induction m with
  | zero => rewrite [zero_add, pow_zero, one_mul]; rfl
  | succ m' ih => rewrite [pow_succ, succ_add, pow_succ, ih, mul_assoc]; rfl

lemma mul_pow (a b n : 𝕟) : (a * b) ^ n = a ^ n * b ^ n :=
  by induction n with
  | zero => rewrite [pow_zero, pow_zero, pow_zero, mul_one]; rfl
  | succ n' ih => rewrite [pow_succ, ih, pow_succ, pow_succ, mul_assoc, mul_comm b, mul_assoc, ←mul_assoc, mul_comm _ b]; rfl

lemma pow_pow (a m n : 𝕟) : (a ^ m) ^ n = a ^ (m * n) := 
 by induction n with 
 | zero => rewrite [mul_zero, pow_zero, pow_zero]; rfl
 | succ n' ih => rewrite [pow_succ, ih, ←pow_add, ←mul_succ]; rfl

lemma add_squared (a b : 𝕟) : (a + b) ^ (2 : 𝕟) = a ^ (2 : 𝕟) + b ^ (2 : 𝕟) + (2 * a * b) :=
  by rewrite [two_eq_succ_one, one_eq_succ_zero, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_zero, mul_one, pow_zero, mul_one, pow_zero, mul_one, add_mul, mul_add, mul_add, mul_comm b a, add_right_comm, add_comm (a * b), add_assoc, add_assoc, add_same, ←add_assoc, ←one_eq_succ_zero, ←two_eq_succ_one, ←mul_assoc]; rfl