/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro 

example : false := _    -- trick question? why?

/-
yes, there is no proof of false

-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
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
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P, 
	apply iff.intro _ _,
	assume porp, 
	apply and.elim porp, 
	assume p, 
  assume p,
  exact p,
	--backwards 
	assume p, 
	exact and.intro P p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P,
  apply iff.into _ _,
  assume porp,

end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


