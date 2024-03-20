variables P Q R S :Prop
theorem swap : (P → Q → R) → (Q → P → R) :=
begin
  assume f q p,
  apply f,
  exact p,
  exact q,
end

#print swap

