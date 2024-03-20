variables P Q: Prop
example : P → P ∨ Q :=
begin
  assume p,
  left,
  exact p,
end

example : Q → P ∨ Q :=
begin
  assume q,
  right,
  exact q,
end