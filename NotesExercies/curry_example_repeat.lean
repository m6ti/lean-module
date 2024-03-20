variables P Q R : Prop
theorem curry : P ∧ Q → R ↔ P → Q → R :=
begin
  constructor,
  assume pnqir,
  assume p,
  assume q,
  apply pnqir,
  constructor,
  exact p,
  exact q,

  assume pqr,
  assume pnq,
  cases pnq,
  apply pqr,
  exact pnq_left,
  exact pnq_right,
end