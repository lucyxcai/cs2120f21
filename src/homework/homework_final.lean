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


def sqr : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := ((nat.succ n') * (nat.succ n')) 

def summed : ℕ → ℕ 
| (nat.zero) := nat.zero                
| (nat.succ n') := (summed n') + (sqr n'.succ) 

def P : ℕ → Prop := 
  λ n, summed n = (1/6) * (n * (1+n) * (1+2*n))

theorem sum_of_n_sq : ∀ n, P n :=
begin
assume n,
unfold P,
induction n with n' ih_n',
apply rfl,
simp [summed],
simp [sqr],  
rw ih_n',              
rw nat.succ_eq_add_one,
ring,
sorry, 
-- by simple arithmetic

end




/-
#2: Formal or detailed informal proofs 10-13

10.Give an informal but detailed proof that for every natural number 𝑛, 1⋅𝑛=𝑛, using a proof by induction, the definition of multiplication, and the theorems proved in Section 17.4.

By induction on n. 1 * 0 = 0 by the first defining clause for multiplication (m*0=0). 
And assuming 1 * n=n, we have 1 * succ(n) = 1 * n + 1 by the second defining clause for multiplication (m * succ(n) = m * n + m). 

11.Show that multiplication distributes over addition. In other words, prove that for natural numbers 𝑚, 𝑛, and 𝑘, 𝑚(𝑛+𝑘)=𝑚𝑛+𝑚𝑘. You should use the definitions of addition and multiplication and facts proved in Section 17.4 (but nothing more).

For natural numbers 𝑚, 𝑛, and 𝑘,  𝑚(𝑛+𝑘)=𝑚𝑛+𝑚𝑘. 
By induction on k. In the case where k=0, mn = mn. In the induction step, we have 
m(n + succ(k)) = m (succ(n+k))
= m * (n+k) + m 
= mn  + mk + m 
= mn + m (succ(k))
using the inductive hypothesis, second defining clause of addition, and the second defining clause of multiplication. 

12.Prove the multiplication is associative, in the same way. You can use any of the facts proved in Section 17.4 and the previous exercise.

For natural numbers m, n, and k, (𝑚𝑛)𝑘=𝑚(𝑛𝑘). 
By induction on k. In the case where k = 0, 0=0 using the proposition in problem 10. In the induction step, we have
(mn)succ(k) = mn * k + mn 
= mnk + mn 
= m (nk + n)
= m (n * succ(k))
using the inductive hypothesis, second defining clause of addition, and the second defining clause of multiplication. 


13.Prove that multiplication is commutative.

For natural numbers n and m, 𝑚𝑛=𝑛𝑚. 
By induction on n. The base case can by implied using the proposition in problem 10. In the induction step, we have
m*succ(n) = m * n + m
= mn + m 
= (n+1)m 
= succ(n)m 
using the inductive hypothesis, the proposition above, and the second defining clause of multiplication. 

#3 (Extra Credit): #5 or #9

prove Cassini’s identity: for every 𝑛, 𝐹^2_𝑛+1−𝐹_𝑛+2𝐹_𝑛=(−1)^𝑛. Hint: in the induction step, write 𝐹^2_𝑛+2 as 𝐹_𝑛+2(𝐹_𝑛+1+𝐹_𝑛)
For n=1: 
1 - (2)(1) = -1^1
1 - 2 = -1
-1 = -1 
Holds true for n = 1. 
In the induction step: 
F_n*F_n+2 - F^2_n+1 = (-1)^n+1
By the Fibonacci sequence rule, F_n+2 = F_n+1 + F_n, F_0=0, F_1=1
F_n+1 = F_n + F_n-1
∴ 
F_n*F_n+2 - F^2_n+1 = F_n*(F_n+1 + F_n) - (F_n+-F_n-1)^2
= Fn*F_n+1 + F^2_n -F^2_n -F^2_n-1 -2F_nF_n-1 
= (F_n+ F_n-1)F_n -F^2_n-1 -2F_nF_n-1
= F^2_n + F_nF_n-1 -F^2_n-1 -2F_nF_n-1
= F^2_n - F_nF_n-1 -F^2_n-1 
= F^2_n -F_n-1 (F_n + F_n-1) 
= F^2_n - F_n-1(F_n+1)

Plug in to the original statement: 
F_n*F_n+2 - F^2_n+1 = -(F_n-1F_n+1 - F^2_n) = -(-1)^n = (-1)^n+1

Cassini's identity holds true. 

NOT FINALIZED. ADVISORY. 
-/