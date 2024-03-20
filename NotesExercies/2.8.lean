variables P Q R :Prop 
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  constructor, --split into 2 parts. Forward and Backward.
  assume h : P ∧ (Q ∨ R) ,
  -- assume the first part of the implication.
  cases h with p qror, --split the AND from the assumption into two parts
  cases qror with q r, --then further split the OR into two parts
  left, -- prove the left side of the OR from what needs to be proved.
  constructor, 
  exact p,
  exact q,
  right, -- prove the right side of the OR from what needs to be proved.
  constructor,
  exact p,
  exact r,

  -- Then solve the other half.
  
  assume h,
  cases h with pnq pnr,
  cases pnq with p q,
  constructor,
  exact p,
  left,
  exact q,
  cases pnr with p r,
  constructor,
  exact p,
  right,
  exact r,
  -- HAHAHAH YESSSS!!
end