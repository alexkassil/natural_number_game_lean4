import MyNat
import MyNat.addition_world
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs

namespace MyNat

lemma mul_zero (a : 𝕟) : a * zero = zero := by rfl
lemma mul_succ (a b : 𝕟) : a * succ b = a + (a * b) := by rfl

lemma zero_mul (m : 𝕟) : zero * m = zero :=
  by induction m with 
  | zero => rewrite [mul_zero]; rfl
  | succ m' ih => rewrite [mul_succ, ih, zero_add]; rfl

@[simp]
lemma mul_one (m : 𝕟) : m * 1 = m := 
  by rewrite [one_eq_succ_zero, mul_succ, mul_zero, add_zero]; rfl

@[simp]
lemma one_mul (m : 𝕟) : 1 * m = m :=
  by induction m with
  | zero => rewrite [mul_zero]; rfl
  | succ m' ih => rewrite [mul_succ, ih, add_comm, succ_eq_add_one]; rfl

@[simp]
lemma mul_add (t a b : 𝕟) : t * (a + b) = t * a + t * b :=
  by induction b with 
  | zero => rewrite [mul_zero, add_zero, add_zero]; rfl
  | succ b' ih => rewrite [add_comm, succ_add, mul_succ, add_comm b' a, ih, ←add_assoc, add_right_comm, ← mul_succ, add_comm]; rfl

@[simp]
lemma mul_assoc (a b c : 𝕟) : (a * b) * c = a * (b * c) := 
  by induction c with
  | zero => rewrite [mul_zero, mul_zero, mul_zero]; rfl
  | succ c' ih => rewrite [mul_succ, mul_succ, mul_add, ih]; rfl

lemma succ_mul (a b : 𝕟) : (succ a) * b = a * b + b := 
  by induction b with 
  | zero => rewrite [mul_zero, mul_zero, add_zero]; rfl
  | succ b' ih => rewrite [mul_succ, mul_succ, ih, ←add_assoc, add_right_comm, succ_add, add_comm a b', ←succ_add, add_comm (succ b') a, add_right_comm]; rfl

lemma add_mul (a b t : 𝕟) : (a + b) * t = a * t + b * t :=
  by induction t with
  | zero => rewrite [mul_zero, mul_zero, mul_zero, add_zero]; rfl
  | succ t' ih => rewrite [mul_succ, ih, add_right_comm, ←add_assoc, ←mul_succ, add_right_comm, add_assoc, ←mul_succ]; rfl

lemma add_same (m : 𝕟) : m + m = 2 * m :=
  by rewrite [←one_mul m, ←add_mul, one_eq_succ_zero, succ_add, zero_add, ←one_eq_succ_zero, ←two_eq_succ_one, one_mul]; rfl

@[simp]
lemma mul_comm (a b : 𝕟) : a * b = b * a := 
  by induction b with
  | zero => rewrite [mul_zero, zero_mul]; rfl
  | succ b' ih => rewrite [mul_succ, succ_mul, ih, add_comm]; rfl

@[simp]
lemma mul_left_comm (a b c : 𝕟) : a * (b * c) = b * (a * c) :=
  by rewrite [mul_comm, mul_assoc, mul_comm c a]; rfl

instance : CommMonoid 𝕟 where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

instance : Monoid 𝕟 := inferInstance

instance : CommSemiring 𝕟 where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one

attribute [simp] mul_assoc

example (a b c d e : 𝕟) :
  (((a * b) * c) * d) * e = (c * ((b * e) * a)) * d := by
  simp only [mul_comm, mul_left_comm]