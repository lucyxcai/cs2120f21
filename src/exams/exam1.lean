/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
      (p2q p) : Q
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume pq, 
  assume p, 
  show Q, 
  from pq p, 
end

-- Extra credit [2 points]. Who invented this principle?

-- Theophrastus

-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- The introduction rule for true gives us a proof of true without conditions

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := 
begin
  exact true.intro,
end 


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- The introduction rule for ∧ derives a proof of P and Q from a proof of P and a proof of Q

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.

Inference rule: 
( P Q: Prop ) (pq : P ∧ Q)
--------------------------- and.elim_left
          p : P
( P Q: Prop ) (pq : P ∧ Q)
--------------------------- and.elim_right
          q : Q
English: The elimination rule for ∧ provides a proof of P and a proof of Q using and.elim_left
and and.elim_right, respectively, given a proof of P ∧ Q. 
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P →P := 
begin
  assume P Q, 
  assume qap, 
  apply and.elim_right qap, 
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- The introduction rule for ∀ states that the predicate 
Q is true for any value t of type T. It assumes an arbritary 
value t of type T and shows that the predicate Q is true 
for that assumed value. Since the value is arbitrary, this 
predicate Q is thus true for all values of type T. 

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (pf t) :  Q t

-- ∀ elimination says that if a predicate Q is true for all 
values of type T, then this predicate must also be true
for a specific value t of type T. Thus, this problem 
shows that given a proof pf of ∀ T, Q and a proof t : T, 
we can conclude Q

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- If you have a proof pf of ∀ T, Q and a value t : T, 
then you can use ∀ elimination to conclude Q. 
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
(Lynn : Person)
(LynnLogic : KnowsLogic Lynn)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/

example : (∃ (Lynn : Person), KnowsLogic Lynn) → (∃ (Lynn : Person), (BetterComputerScientist Lynn)) :=
begin 
  assume h,
  cases h with p pk,
  apply exists.intro p, 
  apply LogicMakesYouBetterAtCS p, 
  exact pk, 
end

-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/- --answer
The proof strategy of proof by negation is essentially the
introduction rule for false, and one can use this strategy to 
prove a proposition ¬P by first assuming a proof of P 
and showing that you can construct a proof of false, or ¬P. 
In other words, this strategy takes a proof of P and returns
a proof of false, which is a proof of ¬P. 
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that ¬P→false.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classically valid, and that accepting the axiom
of the excluded middle suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/


example : ∀ (P Q : Prop), (P↔Q) → (Q↔P) :=
begin
  assume P Q, 
  assume PQ, 
  cases PQ with pq qp, 
  apply iff.intro, 
  exact qp, 
  exact pq,
end 


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
/- English rendition:
For all objects of type Person, if the Person is Nice and
Talented, then all objects of type Person like this Person.
-/
example : ELJL :=
begin
  assume p, 
  intros, 
  apply elantp, 
  exact JLNT.1, 
  exact JLNT.2,
end 



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
- car is heavy and red 
- car is heavy and blue
- car is light and red
- car is light and blue 

-/ 

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x=y→y=x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x=y → y=z → x=z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/
open classical
#check em 

def negelim_equiv_exmid : Prop :=
  ∀ (P : Prop), (¬¬P→P) ↔  (P ∨ ¬P) 
  
example : negelim_equiv_exmid :=
  begin
    assume P,
    apply iff.intro, 
    --forward
    assume nnp, 
    cases em P with p np, 
    exact or.inl p, 
    exact or.inr np, 
    --backward
    assume pornp, 
    assume nnp,
    cases em P with p np, 
    exact p,
    contradiction,

  end

/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∃ (p : Person), ∀ (ev : Person), Loves ev p) → (∃ (p : Person), ∀ (e : Person), Loves p e) := 
begin 
  assume h, 
  cases h with p evl, 
  apply exists.intro p, 
  assume e,
end