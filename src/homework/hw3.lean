/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

<<<<<<< HEAD
example : true := true.intro 
=======
example : true := true.intro
>>>>>>> 36448287f7f33dcb7d4182fcc8163977e44bf41a

example : false := _    -- trick question? why?

/-
yes, there is no proof of false

-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
<<<<<<< HEAD:src/homework/practice_2.lean
  assume P, 
<<<<<<< HEAD
	apply iff.intro _ _,	
	-- forward P∨P -> P
		assume porp,
		apply or.elim porp,	
		-- left disjunct is true P∨P
		assume p, 	
		exact p,			
		-- right disjunct is true
    assume p,
    exact p,
	-- backwards P -> P∨P	//assume P, then proof P∨P is true
		assume p,	
		exact or.intro_left P p, 	
=======
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
>>>>>>> 36448287f7f33dcb7d4182fcc8163977e44bf41a
=======
>>>>>>> 289938d4d64bfdbe1db71208069fe4a3145149fc:src/homework/hw3.lean
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P, 
	apply iff.intro _ _,
	assume pandp, 
	apply and.elim pandp, 
	assume p, 
  assume p, 
  exact p,
	--backwards 
	assume p, 
	exact and.intro p p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  assume porq,
  apply or.elim porq,
  assume pq, 
  exact pq,
  assume pq,
  exact pq,
  assume pq,
  exact or.intro_left P pq,
  exact or.intro_right Q pq,

end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P, 
  assume Q, 
	apply iff.intro _ _,
	assume pandp, 
	apply and.elim pandp, 
	assume pq,
  exact pq,
  assume pq,
  exact pq,
	--backwards 
	assume pq, 
	exact and.intro pq pq,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P,
  assume Q,
  assume R, 
  apply iff.intro _ _,
  assume pandp,
  apply and.elim pandp,
  assume porp,
  apply or.elim porp,
  assume pqr,
  exact pqr, 
  assume pqr,
  exact pqr,
  assume pqr,
  exact and.intro pqr pqr,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P,
  assume Q,
  assume R, 
  apply iff.intro _ _,
  assume pandp,
  apply and.elim pandp,
  assume porp,
  apply or.elim porp,
  assume pqr,
  exact pqr, 
  assume pqr,
  exact pqr,
  assume pqr,
  exact or.intro_left PQR pqr,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  assume pandp,
  apply and.elim pandp,
  assume porp,
  apply or.elim porp,
  assume pq,
  exact pq, 
  assume pq,
  exact pq,
  assume pq,
  exact and.intro pq pq,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P,
  assume Q,
  apply iff.intro _ _,
  assume pandp,
  apply and.elim pandp,
  assume porp,
  apply or.elim porp,
  assume pq,
  exact pq, 
  assume pq,
  exact pq,
  assume pq,
  exact or.intro_left PQ pq,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  assume true,
  apply iff.intro _ _,
  assume porp,
  apply or.elim porp,
  assume p,
  exact p,
  assume p, 
  exact p,
  assume p,
  exact or.intro_left P p,

end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  --No answer because false is never true there is no proof of false
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  assume true, 
  apply iff.intro _ _,
  assume pandp,
  apply and.elim pandp,
  assume p,
  assume p,
  exact p,
  assume p,
  exact and.intro p p,

end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
    --No answer because false is never true there is no proof of false
end


