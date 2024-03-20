variables P Q :Prop
example : P → (Q → (P ∧ Q)) :=
begin
  assume p q,
  constructor,
  exact p,
  exact q,
end
--    | P  | Q  | PnQ | Q->(PnQ) | P → (Q → (P ∧ Q))
--    | 0  | 0  | 0   |    1     | T
--    | 0  | 1  | 0   |    0     | T
--    | 1  | 0  | 0   |    1     | T
--    | 1  | 1  | 1   |    1     | T
