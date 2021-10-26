import data.set
#check @set.ext 
/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ {α : Type} (L : set α), ((L ∩ L) = L) := 
begin
  intros α L, 
  apply set.ext _,

  assume x, 
  split, 
  
  assume h, 
  cases h with l r, 
  exact l, 

  assume j,
  exact and.intro j j, 

end 


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

/-
For all values of type α, if L and X are sets containing α values and L is a subset of X, then
we can get a proof of L = X by applying the commutative property to the union operator. 
We will have a proof of L = X, with only the proof of ∀ x, x ∈ L ↔ x ∈ X remaining 
to be produced.
-/

example : ∀ {α : Type} (L X : set α), L ⊆ X → ((L ∩ X) = L) := 
begin
  intros α L X h,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with l r,
  exact l,
  -- backward
  assume k,
  exact and.intro k (h k),
end 

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example : ∀ {α : Type} (L X : set α), L ⊆ X → X ⊆ L →L ⊆ L :=
begin
  intros α L X h, 
  assume x, 
  assume a, 
  assume y, 
  exact y, 
end  

/-
For all values of type α, and L X are sets of type α, if L has a subset of X 
and X has a subset of L, then L has a subset of L, proving has_subset ⊆ is both
reflexive and transitive. 
-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example : ∀ {α : Type} (L M R : set α ),(L ∩ M) ∪ (M ∩ R) = M ∪ (L ∩ R) :=
begin
  intros α L M R, 
  apply set.ext _,
  assume x, 
  split, 
  assume h, 
  cases h with l r, 
  apply or.inl, 
  exact and.elim_right l, 
  apply or.inr, 
  apply and.intro,  --question
end 


/-
Assignment: read (at least skim) the Sections 1 and 
2 of the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state, and prove both formally and 
informally, that ∩ is left-distributive over ∩.
-/

/- 
Given sets L M R of type α, if L ∩ (M ∩ R) then L ∩ M) ∩ (L ∩ R), proving a left
distribution of ∩ over ∩. 
-/
example : ∀ {α : Type} (L M R : set α ), L ∩ (M ∩ R) = (L ∩ M) ∩ (L ∩ R) :=
begin 
  intros α L M R, 
  apply set.ext _,
  assume x,
  split, 
  assume h, 
  cases h with l r, 
  apply and.intro, 
  exact and.intro l (and.elim_left r),
  exact and.intro l (and.elim_right r),

  assume j, 
  cases j with l r, 
  apply and.intro, 
  exact and.elim_left l, 
  apply and.intro,
  exact and.elim_right l, 
  exact and.elim_right r, 

end

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example : ∀ {α : Type} (L M R : set α ), L ∪ (M ∩ R) = (L ∪ M) ∩ (L ∪ R) :=
begin 
  intros α L M R, 
  apply set.ext _,
  assume x, 
  split, 
  assume h, 
  cases h with l r, 
  apply and.intro, 
  apply or.inl, 
  exact l, 
  apply or.inl, 
  exact l, 

  apply and.intro, 
  apply or.inr, 
  exact and.elim_left r, 

  apply or.inr, 
  exact and.elim_right r, 
  
  assume m, 
  cases m with l r, 
  apply or.inl, 
  cases l, 
  exact l, 
  cases r, 
  exact r,--question
end

/- 
Given sets L M R of type α, if L ∪ (M ∩ R)  then (L ∪ M) ∩ (L ∪ R), proving a left
distribution of ∪ over ∩. 
-/

