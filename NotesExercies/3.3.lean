open classical

variables P Q: Prop
theorem raa : ¬ ¬ P -> P :=
begin 
  assume nnp,
  --assume ¬ ¬ P to then prove P by analysing P ∨ ¬ P
  cases (em P) with p np,
  -- in the case p, we can exact p, and in case ¬ p,
  -- we have a contradiction with ¬ ¬ P, and we can use that
  -- false implies everything
  exact p,
  have f: false,
  apply nnp,
  exact np,
  cases f,
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

constant raa2 : ¬ ¬ P -> P

theorem em : P ∨ ¬P :=
begin
  apply raa,
  apply nn_em,
end

-- Very nice 👍

