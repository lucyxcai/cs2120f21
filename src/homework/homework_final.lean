import algebra.algebra.basic tactic.ring

/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.

Write the principle of complete induction using the notation of symbolic logic.

P(n) means that P holds of n:
P(0)∧ ∀n (P(n-1)→ P(n))→ ∀nP(n)

#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 

    Show that for every 𝑛, 0^2 + 1^2 + 2^2 + … 𝑛^2 = 1/6 𝑛(1+𝑛)(1+2𝑛).

Statement P(n): 0^2 + 1^2 + 2^2 + … 𝑛^2 = 1/6 𝑛(1+𝑛)(1+2𝑛) for n ∈ ℕ 
For n=1: 1^2 = 1/6 (1+1)(1+2)
    1 = 1/6 (2)(3)
    1 = 1
    So P(1) is true. 
By proof of induction, we add (n+1)^2 to both sides of P(n):
0^2 + 1^2 + 2^2 + … 𝑛^2 + (n+1)^2 = 1/6 𝑛(1+𝑛)(1+2𝑛) + (n+1)^2
Left hand side = 
1/6 n(1+n)(1+2n) + (n+1)^2 = (substitute P(n) in)
(n+1)[(n(2n+1)/6 + (n+1))] = 
(n+1)(2n^2 +7n + 6)/6 = 
(n+1) [(n+2)(2n+3) ]/6 
Right hand side = 
[(n+1) (n+2)(2n+3)]/6
∴ Left hand side = right hand side → [(n+1) (n+2)(2n+3)]/6 =[(n+1) (n+2)(2n+3)]/6
so for n∈ℕ, the statement P(n) holds true. 


-/

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.

Show that for every 𝑛, 0^2+1^2+2^2+…𝑛^2=16𝑛(1+𝑛)(1+2𝑛).

-/



/-
#2: Formal or detailed informal proofs 10-13

Give an informal but detailed proof that for every natural number 𝑛, 1⋅𝑛=𝑛, using a proof by induction, the definition of multiplication, and the theorems proved in Section 17.4.

By induction on n. 1 * 0 = 0 by the first defining clause for multiplication (m*0=0). 
And assuming 1 * n=n, we have 1 * succ(n) = 1 * n + 1 by the second defining clause for multiplication (m * succ(n) = m * n + m). 

Show that multiplication distributes over addition. In other words, prove that for natural numbers 𝑚, 𝑛, and 𝑘, 𝑚(𝑛+𝑘)=𝑚𝑛+𝑚𝑘. You should use the definitions of addition and multiplication and facts proved in Section 17.4 (but nothing more).

Prove the multiplication is associative, in the same way. You can use any of the facts proved in Section 17.4 and the previous exercise.

Prove that multiplication is commutative.

#3 (Extra Credit): #5 or #9

Let 𝑉 be a non-empty set of integers such that the following two properties hold:

If 𝑥,𝑦∈𝑉, then 𝑥−𝑦∈𝑉.

If 𝑥∈𝑉, then every multiple of 𝑥 is an element of 𝑉.

Prove that there is some 𝑑∈𝑉, such that 𝑉 is equal to the set of multiples of 𝑑. Hint: use the least element principle.

NOT FINALIZED. ADVISORY. 
-/