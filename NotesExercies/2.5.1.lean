variables P Q : Prop
theorem comAnd : P ∧ Q → Q ∧ P :=
begin
  assume pq,
  cases pq with p q,
    constructor,
    exact q,
    exact p
end


theorem comAndIff : P ∧ Q ↔ Q ∧ P :=
begin
  constructor,
  apply comAnd,
  apply comAnd,
end