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
  have f : false := h (eq.refl 0),
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

end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q, 
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
  assume P Q R,
  apply iff.intro, 

  --forward
  assume poqapor, 
  have poq := poqapor.1, 
  cases poq with p q, 
    apply or.elim, 
  have por := poqapor.2,
  cases por with p r, 
    apply or.elim, 
  exact or.elim p (and.intro q r), 
  --backward
  assume poqar, 
  have p := poqar.1,
  have qar := poqar.2,
  cases qar with q r, 
  exact or.elim p q, 
  exact or.elim p r,



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
  --forward
  assume poqaros,
  have poq := and.elim_left poqaros, 
  have ros := and.elim_right poqaros, 
  have p := or.inl poq,
  have q := or.inr poq, 
  have r := or.inl ros, 
  have s := or.inr ros, 
  exact or.elim (and.intro p r) (and.intro p s), 
  exact or.elim (and.intro p s) (and.intro q r),
  exact or.elim (and.intro q r) (and.intro q s),  
  --backward
  assume back, 
  apply or.elim back, 
  assume par, 
  have p := par.left, 
  have r := par.right, 
  show (P ∨ Q) ∧ (R ∨ S), 
  from ⟨and.elim_left p, and.elim_right r⟩, 
  assume pas, 
  have p := par.left, 
  have s := par.right, 
  show (P ∨ Q) ∧ (R ∨ S), 
  from ⟨and.elim_left p, and.elim_right s⟩, 
  assume qar, 
  have q := par.left, 
  have r := par.right, 
  show (P ∨ Q) ∧ (R ∨ S), 
  from ⟨and.elim_left q, and.elim_right r⟩, 
  assume qas, 
  have q := par.left, 
  have s := par.right, 
  show (P ∨ Q) ∧ (R ∨ S), 
  from ⟨and.elim_left q, and.elim_right s⟩, 

end

/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀(n : ℕ ), n =0 ∨ n ≠ 0 :=
begin
  assume h, 
  have f : false := (or.inl h),
  exact false.elim (f),
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q p q,
  apply iff.intro, 
  show ¬P ∨ Q, 
  from ⟨ np, q ⟩, 

end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q, 
  assume pimq,
  assume nqimnp, 
  exact pimq,
  exact nqimnp, --question
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npnq,
  assume qimp, 
  exact npnq, 
  exact qimp,
end

