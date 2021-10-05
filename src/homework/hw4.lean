-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  trivial,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have zeqz := eq.refl 0,
  have f : false := h zeqz,
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
<<<<<<< HEAD
    assume P Q, 
    apply iff.intro _ _,
    /- forward -/
        assume npaq,
        cases em P with p np,
        cases em Q with q nq,
        have f : false := npaq (and.intro p q),
        exact false.elim f,
        exact or.inr nq,
        exact or.inl np,
    /-backward-/
        assume nponq,
        assume paq,
        cases nponq with np nq,
        have p := paq.left,
        have f : false := np p,
        exact false.elim f,
        have q := paq.right,
        have f : false := nq q,
        exact false.elim f,

=======
  assume P Q,
  split,
  -- forward
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have pq := and.intro p q,
  contradiction,
  exact or.inr nq,
  exact or.inl np,
  -- backward
  admit,
>>>>>>> 128dfadb3912953944b27845e11e6852382f329d
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → (¬P ∧ ¬Q) :=
begin
<<<<<<< HEAD
  assume P Q, 
      assume npoq,
      cases em P with p np,
      have f : false := npoq (or.inl p),
      exact false.elim f,
      cases em Q with q nq,
      have f : false := npoq (or.inr q),
      exact false.elim f,
      exact and.intro np nq,
=======
  assume P Q,
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have porq := or.intro_left Q p,
  contradiction,
  have porq := or.intro_left Q p,
  contradiction,
  cases (classical.em Q) with q nq,

>>>>>>> 128dfadb3912953944b27845e11e6852382f329d
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pnpq,
  apply or.elim pnpq,
  assume p,
  apply or.inl p,
  
  assume npq,
  apply and.elim npq,
  assume np,
  assume q,
  apply or.inr q,

  assume pq,
  apply or.elim pq,
  assume p,
  apply or.inl p,

  assume q,
  cases em P with p np,
  apply or.inl p,
  have pq := and.intro np q,
  apply or.inr pq,
  
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
assume e,
apply iff.intro,
    have pq := and.elim_left e,
    apply or.elim pq,
    assume p,
    apply or.inl p,
    have pr := and.elim_right e,

    apply or.elim pr,
    assume p,
    assume q,
    apply or.inl p,
    assume r,
    assume q,
    have qr := and.intro q r,
    apply or.inr qr,


end


-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S, 
  apply iff.intro, 
  assume poqaros, 
  have poq := poqaros.left,
  have ros := poqaros.2, 

  cases poq, 
  cases ros, 
  apply or.inl, 
  exact and.intro poq ros, 

  apply or.inr, 
  apply or.inl, 
  exact and.intro poq ros, 

  cases ros, 
  apply or.inr, 
  apply or.inr, 
  apply or.inl,
  exact and.intro poq ros, 

  apply or.inr, 
  apply or.inr, 
  apply or.inr, 
  exact and.intro poq ros, 

  --backwards

  assume h, 
  apply or.elim h, 
  assume par, 
  have p := par.1, 
  have r := par.2, 

  apply and.intro,
  exact or.inl p, 
  exact or.inl r, 

  assume h1, 
  apply or.elim h1,
  assume pas, 
  have p := pas.1,
  have s := pas.2, 
  apply and.intro, 
  exact or.inl p, 
  exact or.inr s, 
  
  assume h2, 
  apply or.elim h2,  
  assume qar, 
  have q := qar.1, 
  have r := qar.2, 
  apply and.intro,
  exact or.inr q, 
  exact or.inl r, 

  assume qas, 
  have q := and.elim_left qas, 
  have s := and.elim_right qas, 
  apply and.intro,
  exact or.inr q, 
  exact or.inr s, 

end

/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ (∀ (n : ℕ ), (n=0)) :=
begin
  assume e, 
  have oez := e 1, 
  contradiction, 
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume e,
  cases em Q with q nq,
  apply or.inr q,

  apply or.intro_left,
  cases em P with p np,
  have q := (e p),
  contradiction,

  assume p,
  contradiction,

  assume e2,
  apply or.elim e2,
  assume np,
  assume p,
  contradiction,

  assume q,
  assume p,
  exact q,
end


-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume e, 
  assume nq,
  assume p,
  cases em Q with q nq, 
  contradiction,

  have q := (e p),
  contradiction,
end

-- 13 (c)
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume h,
  assume q,

  cases em P with p np,
  exact p,

  have nq := (h np),
  contradiction,
end



axioms (T : Type) (Q : Prop) (f : ∀ (t : T), Q) (t : T)
example : Q := f t
#check f
