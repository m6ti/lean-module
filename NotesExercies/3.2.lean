open classical

variables P Q :Prop

theorem dm2_em : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
begin
  assume npq,
  cases em P with p np,
  right,
  assume q,
  apply npq,
  constructor,
  exact p,
  exact q,
  left,
  exact np,
end