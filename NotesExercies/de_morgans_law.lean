variables P Q :Prop
theorem dm1 : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  constructor,
  assume npoq,
  constructor,
  assume p,
  apply npoq,
  left,
  exact p,
  assume q,
  apply npoq,
  right, 
  exact q,
  assume npnq,
  cases npnq with np nq,
  assume n,
  cases n with p q,
  apply np,
  exact p,
  apply nq,
  exact q,
end

theorem dm2 : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  constructor,
  assume npoq,
  constructor,
  assume p,
  apply npoq,
  constructor,
  exact p,
  sorry,
  
  cases npoq with np nq,

end
