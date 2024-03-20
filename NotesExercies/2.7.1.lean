variables P Q R : Prop
theorem case_lem : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  assume p2r q2r pq,
  cases pq with p q,
  apply p2r,
  exact p,
  apply q2r,
  exact q,
end