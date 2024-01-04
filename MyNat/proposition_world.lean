import MyNat.lemma
open Lean Core

namespace MyNat

example (P Q : Prop) (p : P) (h : P → Q) : Q := by
  exact h p

lemma imp_self (P : Prop) : P → P := by
  intro p
  exact p

lemma maze1 (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U := by
  exact l (j (h p))

lemma maze2 (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U := by
  apply l
  apply j
  apply h
  exact p 

example (P Q : Prop) : P → (Q → P) := by
 intro p _
 exact p

example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  intro a b c
  exact (a c (b c))

lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  intro hpq hqr p
  exact hqr (hpq p)

lemma not_iff_imp_false (P : Prop) : ¬ P ↔ (P → False) := by
  rewrite [Not]
  exact Iff.rfl

lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  rewrite [not_iff_imp_false, not_iff_imp_false]
  intro a b c
  apply b
  apply a
  exact c

example (A B C D E F G H I J K L : Prop)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L := by
  intro a
  exact f15 (f11 (f9 (f8 (f5 (f2 (f1 a))))))
