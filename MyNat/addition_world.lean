/-
  a type called MyNat
  a term 0 : MyNat, which is the number zero
  a function succ : MyNat -> MyNat, which is +1
  Use numerical notation, 0, 1, 2, ...
  Use + and * to represent addition and multiplication
  lemmas we already proved (add_zero, add_succ, and zero_succ_add)
  tactics rewrite and rfl
-/

import MyNat
import MyNat.lemma
import MyNat.tutorial_world
import Mathlib.Algebra.Group.Defs

namespace MyNat

lemma zero_add (n : 𝕟) : zero + n = n :=
  by
  induction n with 
  | zero => rewrite [add_zero]; rfl
  | succ n' ih => rewrite [add_succ, ih]; rfl

lemma add_assoc (a b c : 𝕟) :
  (a + b) + c = a + (b + c) :=
  by
  induction c with
  | zero => rewrite [add_zero, add_zero]; rfl
  | succ c' ih => rewrite [add_succ, add_succ, add_succ, ih]; rfl

lemma succ_add (a b : 𝕟) : succ a + b = succ (a + b) :=
  by induction b with 
  | zero => rewrite [add_zero, add_zero]; rfl
  | succ b' ih => rewrite [add_succ a b', <- ih, add_succ]; rfl

lemma add_comm (a b : 𝕟) : a + b = b + a :=
  by induction b with
  | zero => rewrite [add_zero, zero_add]; rfl
  | succ b' ih => rewrite [add_succ, succ_add, ih]; rfl

lemma one_eq_succ_zero : 1 = succ zero := by rfl
lemma two_eq_succ_one :  2 = succ 1    := by rfl

lemma succ_eq_add_one (n : 𝕟) : succ n = n + 1 :=
  by induction n with
  | zero => rewrite [one_eq_succ_zero, zero_add]; rfl
  | succ n' ih => rewrite [ih, <- succ_add, ih]; rfl

lemma add_right_comm (a b c : 𝕟) : a + b + c = a + c + b :=
  by rewrite [add_assoc, add_comm b c, add_assoc a c b]; rfl

instance : AddMonoid 𝕟 where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero

instance : AddCommMonoid 𝕟 where
  add_comm := add_comm
