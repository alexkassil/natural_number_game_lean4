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

open MyNat

lemma zero_add (n : MyNat) : zero + n = n :=
  by
  induction n with 
  | zero => rewrite [add_zero] rfl
  | succ n' ih => rewrite [add_succ, ih] rfl

lemma add_assoc (a b c : MyNat) :
  (a + b) + c = a + (b + c) :=
  by
  induction c with
  | zero => rewrite [add_zero, add_zero] rfl
  | succ c' ih => rewrite [add_succ, add_succ, add_succ, ih] rfl

lemma succ_add (a b : MyNat) : succ a + b = succ (a + b) :=
  by induction b with 
  | zero => rewrite [add_zero, add_zero] rfl
  | succ b' ih => rewrite [add_succ a b', <- ih, add_succ] rfl