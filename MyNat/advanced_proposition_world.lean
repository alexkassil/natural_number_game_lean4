import MyNat

open MyNat

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



