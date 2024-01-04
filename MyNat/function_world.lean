import MyNat

namespace MyNat

example (P Q : Type) (p : P) (h : P -> Q) : Q := by
  exact h p

example : 𝕟 -> 𝕟 := by 
  intro n
  exact 3 * n + 2

example (P Q R S T U: Type)
  (p : P)
  (h : P → Q)
  (i : Q → R)
  (j : Q → T)
  (k : S → T)
  (l : T → U)
  : U := by
  have q := h p
  have t := j q
  have u := l t
  exact u

example (P Q R S T U: Type)
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

example (P Q : Type) : P → (Q → P) := by
  intro p _
  exact p

example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  intro a b c
  have q := b c
  have r := a c q
  exact r

example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) := by
  intro a b c
  apply b
  apply a
  exact c

example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) := by
  intro a b c
  apply b
  apply a
  exact c

example (A B C D E F G H I J K L : Type)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L := by
  intro a
  exact f15 (f11 (f9 (f8 (f5 (f2 (f1 a))))))

