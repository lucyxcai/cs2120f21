-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have zeqz := eq.refl 0,
  contradiction,
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
  contradiction, 
  /- contradiction instead of 
  have f := h p, 
  exact f, 
  -/
  
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
    assume P Q, 
    apply iff.intro,  -- split, 
    assume npaq, 
    cases em P with p np, 
    cases em Q with q nq, 
    have f : false := npaq (and.intro p q),
    exact false.elim f, 
    apply or.inr nq, 
    apply or.inl np, 

    assume nponq, 
    assume paq, 
    cases nponq with np nq, 
    have p := paq.1, 
    have f : false := np p, 
    exact false.elim f, 
    have q := paq.2, 
    have f : false := nq q, 
    exact false.elim f, 


end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P,
  assume Q,
  assume npoq, 
  cases em P with p np, 
  have f : false := npoq (or.inl p), 
  exact false.elim f, 
  cases em Q with q nq, 
  have f : false := npoq (or.inr q), 
  exact false.elim f, 
  exact and.intro np nq, 

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q, 
  split, 
  assume ponpaq, 
  cases ponpaq with p npaq, 
  exact or.inl p, 
  have np := npaq.1, 
  have q := npaq.2, 
  exact or.inr q, 
  assume poq, 
  cases poq with p q, 
  exact or.inl p, 
  cases em P with p np, 
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : _ :=
begin
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
end

def evens : set ℕ := { n | n%2 = 0}

example : ({ 0, 2 } : set ℕ) ⊆ evens := --for all natural numbers, if n is in this set then its in that set too
begin
  --show ∀ n, n=0 ∨ n=2 →n ∈ evens, 
   assume n, 
   assume h,
   cases h, 
   rewrite h, 
   exact rfl, --proof by reflexivity, prove evens applied to 0 is true (0 mod 0 = 0)
   cases h, 
   exact rfl, 
   
end