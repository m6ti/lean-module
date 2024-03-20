variables P Q R : Prop

example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  constructor,
  assume h,
  cases h with p qr,
  cases qr with q r,
  left,
  constructor,
  exact p, 
  exact q,
  right,
  constructor,
  exact p,
  exact r,

  assume h,
  constructor,
  cases h with pq pr,
  cases pq with p q,
  exact p,
  cases pr with p r,
  exact p,

  cases h with pq pr,
  cases pq with p q,
  left,
  exact q,
  cases pr with p r,
  right,
  exact r,
end