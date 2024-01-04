import MyNat
import MyNat.proposition_world

namespace MyNat

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor 
  exact p
  exact q

lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro p q =>
    constructor
    exact q
    exact p

lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases h1 with 
  | intro p q => 
  cases h2 with 
  | intro q r =>
  constructor
  exact p
  exact r

lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  cases h1 with
  | intro pq qp => 
  cases h2 with
  | intro qr rq => 
  constructor
  intro p
  exact (qr (pq p))
  intro r
  exact (qp (rq r))

example (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  constructor 
  intro p
  apply (Iff.mp hqr)
  apply (Iff.mp hpq)
  exact p
  intro r
  rewrite [hpq, hqr]
  exact r

example (P Q : Prop) : Q → (P ∨ Q) := by
 intro q
 exact (Or.inr q)

lemma or_symm (P Q : Prop) : P ∨ Q -> Q ∨ P := by
  intro pq
  exact (
    Or.elim 
    pq
    (Or.inr)
    (Or.inl)
  ) 

lemma alexs_discovery (P Q R : Prop) : 
  P → (P ∨ Q) ∧ (P ∨ R) := by
  intro p
  exact ⟨Or.inl p, Or.inl p⟩

lemma and_or_distrib_left (P Q R : Prop) : 
  P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor 
  intro p_and_qr
  let p := (p_and_qr.left)
  let qr := (p_and_qr.right)
  exact (
    Or.elim qr
    (fun q => Or.inl (And.intro p q))
    (fun r => Or.inr (And.intro p r))
  )
  intro p_and_q_or_p_and_r
  exact (
    Or.elim p_and_q_or_p_and_r
    (fun pq => 
      And.intro pq.left (Or.inl pq.right)
    )
    (fun pr =>
      And.intro pr.left (Or.inr pr.right)
    )
  )

lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro pandnotp
  let p := pandnotp.left
  let notp := pandnotp.right
  -- rewrite [not_iff_imp_false] at notp
  -- let false := (notp p)
  -- exact False.elim false
  exact (absurd p notp)

lemma contrapositive2 (P Q : Prop) : 
  (¬Q → ¬P) → (P → Q) := by 
  intro h p
  by_cases p : P
  case inl p' => 
    . by_cases q : Q
      . case inl => exact q
      . case inr => exact absurd p (h q)
  case inr p' => 
    . by_cases q : Q
      . case _ => exact q
      . case inr => exact absurd p' p

lemma full_contrapositive (P Q : Prop) : 
  (¬Q → ¬P) ↔ (P → Q) := by
  constructor
  exact contrapositive2 P Q
  exact contrapositive  P Q