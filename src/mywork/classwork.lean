def pythagorean_triple (a b c : nat) : Prop :=
a*a + b*b = c*c

example: ε (a b c : ℕ ), pt a b c :=
begin
  unfold pt,
  apply eq.refl,
end

example:  pt 3 4 5 :=