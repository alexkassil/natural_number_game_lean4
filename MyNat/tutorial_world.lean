import MyNat

namespace MyNat

/- For all natural numbers x, y, z, we have x * y + z = x * y + z -/
lemma example1 (x y z: 𝕟) : x * y + z = x * y + z :=
  rfl

lemma example2 (x y: 𝕟) (h: y = x + 7) : 2 * y = 2 * (x + 7) :=
  by
  rewrite [<- h]
  rfl

/- If succ(a) = b, then succ(succ(a)) = succ(b) -/
lemma example3 (a b: 𝕟) (h: succ a = b) : succ (succ a) = succ b :=
  by
  rewrite [h]
  rfl

@[simp]
lemma add_zero (a : 𝕟) : a + zero = a :=
  by rfl

lemma add_succ (a d : 𝕟) : a + succ d = succ (a + d) :=
  by rfl

lemma zero_succ_add (a : 𝕟) : a + succ zero = succ a :=
  by
  rewrite [add_succ, add_zero]
  rfl

end MyNat