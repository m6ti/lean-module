open classical

variables P Q :Prop

/- -/ theorem raa : ¬ ¬ P → P := 
/- -/ begin
/- -/   assume nnp,
/- -/   cases (em P) with p np,
/- -/     exact p,
/- -/     have f : false,
/- -/       apply nnp,
/- -/       exact np,
/- -/     cases f,
/- -/ end

#check em P

example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
begin
  assume npq,
  cases em (P) with p np,
  right,
  assume q,
  apply npq,
  constructor,
  assumption,
  assumption,
  left,
  exact np,
end

example : (¬ P ∨ ¬ Q) →  ¬ (P ∧ Q) :=
begin
  assume npnq,
  assume pnq,
  cases npnq,
  apply npnq,
  cases pnq,
  assumption,
  apply npnq,
  cases pnq,
  assumption,
end

theorem nn_em : ¬ ¬ (P ∨ ¬ P) :=
begin
  assume npnp,
  apply npnp,
  right,
  assume p,
  apply npnp,
  left,
  exact p,
end

theorem em : P ∨ ¬ P :=
begin
  apply raa,
  apply nn_em,
end

example : ¬¬(P ∨ ¬P) → P ∨ ¬ P :=
begin
  assume nnpnp,
  apply raa,
  assumption,
end 
