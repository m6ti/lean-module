/-
COMP2065 Tutorial 2
-/

variables P Q R : Prop

/-
What is a logic?
A particular system or codification of the principles of proof and inference.
* Propositional logic - a formal system where formulae are built by joining
  propositions using logical connectives.
* Classical logic - logic based on truth value (uses truth tables).
* Intuitionistic logic - logic based on evidence. 
* Predicate logic - extends propositional logic and will be covered next week. 

Classical Logic = Intuitionistic Logic + Excluded Middle (em P : P ∨ ¬ P)

It turns out that excluded middle is equivalent to another law, double
negation elimination/reductio ad absurdum (raa P : ¬ ¬ P → P).

The basic tactics seen so far in Lean have all been intuitionistic. In order
to prove classical logic formulae, we have to tell Lean we want to work in
classical logic and access EM by doing the following.
-/

open classical

-- This makes the following available.

-- #check em P

--------------------------------------------------------------------------------
-- PART I : EM & RAA

-- Proof that EM (P ∨ ¬ P) implies RAA (¬ ¬ P → P)

theorem raa : ¬ ¬ P → P := 
begin
  assume h,
  cases em P with h1 h2,
  exact h1,
  have f:false,
  contradiction,
  contradiction,
end

-- Proof that RAA (¬ ¬ P → P) implies EM (P ∨ ¬ P) 

theorem my_em : P ∨ ¬ P :=
begin
  cases em P,
  left,
  assumption,
  right,
  assumption,
end 

-- Any classical logic formula can be proved by assuming either one
-- of EM or RAA.

--------------------------------------------------------------------------------
-- PART II: Examples

/-
3 possible cases: 
* A) provable intuitionistically
* B) provable classically
* C) not provable 
-/     

theorem example_1 : ((P ∨ Q) ∧ ¬ P) → Q :=
begin
  assume h,
  cases h with l r,
  cases l,
  contradiction,
  exact l,
  -- intuitionistically
end  

theorem example_2 : (¬ P → Q) → (¬ Q → P) :=
begin
  assume h1 h2,
  apply raa,
  assume h3,
  apply h2,
  apply h1,
  exact h3,
end 

theorem example_3 : (P → Q) → (Q → P) :=
begin
  sorry
  -- not provable
end

theorem example_4 : (¬ P → P) → P :=
begin
  assume h1,
  apply raa,
  assume h2,
  apply h2,
  apply h1,
  exact h2,
end  

theorem example_5 : ¬ (P ∨ ¬ P) :=
begin  
  sorry
  --not provable.
end

/-
Tips:
* using truth tables tells us whether something is provable or not, but does 
  not tell us whether it is provable intuitionistically or classically 
* when trying to prove something intuitionistically, think of witnesses/evidence
  e.g. ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) vs (¬ P ∨ ¬ Q) → ¬ (P ∧ Q)
-/