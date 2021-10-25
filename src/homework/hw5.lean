import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 
There exists a function f that takes a value of type α and returns a value of type β. For all 
values a of type α in set p, the function f is applied. Thus, we get a set q consisting of 
type β values derived from set p. 
(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
If there's a function that takes every α value that is given and returns a type β value, 
then this proposition takes every α value in set p and returns a set q consisting of β values
after applying the function to each value in set p.  
-/


-- Give your formal proof here
begin
  
  assume h1,
cases h1 with f e,
assume h2,
have e2 := exists_imp_exists e h2,
cases e2 with a qfa,
have b := f a,
apply exists.intro b,
end
  

