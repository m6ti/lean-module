variables P Q R : Prop
theorem curry : P ∧ Q → R ↔ P → Q → R :=
begin
  constructor,
  assume pqr p q,
  apply pqr,
  constructor,
  exact p,
  exact q,
  
  assume pqr pq,
  cases pq with p q,
  apply pqr,
  exact p,
  exact q,
end