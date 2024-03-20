variables P Q R :Prop


theorem C : (P → Q) → (Q → R) → P → R :=
begin
  assume h1,
  assume h2,
  assume h3,
  apply h2,
  apply h1,
  exact h3,
end

theorem swap : (P → Q → R) → (Q → P → R) :=
begin
  assume h1 h2 h3,
  apply h1,
  assumption,
  assumption,
end

example : P → Q → P ∧ Q :=
begin
  assume p q,
  constructor,
  assumption,
  assumption,
end

theorem comAnd : P ∧ Q → Q ∧ P :=
begin
  assume h1,
  cases h1 with l r,
  constructor,
  assumption,
  assumption,
end

theorem comAndIff : P ∧ Q ↔ Q ∧ P :=
begin
  constructor,
  apply comAnd,
  apply comAnd,
end


theorem curry : P ∧ Q → R ↔ P → Q → R :=
begin
  constructor,
  assume h1 h2 h3,
  apply h1,
  constructor,
  assumption,
  assumption,
  assume h1 h2,
  cases h2 with l r,
  apply h1,
  assumption,
  assumption,
end


example : P → P ∨ Q :=
begin
  assume h1,
  left,
  exact h1,
end

theorem case_lem : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  assume h1 h2 h3,
  cases h3,
  apply h1,
  assumption,
  apply h2,
  assumption,
end



example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin 
  constructor,
  assume h1,
  cases h1 with l r,
  cases r,
  left,
  constructor,
  assumption,
  assumption,
  right,
  constructor,
  assumption,
  assumption,
  
  assume h1,
  constructor,
  cases h1,
  cases h1,
  assumption,
  cases h1,
  assumption,
  cases h1,
  left,
  cases h1,
  assumption,
  right,
  cases h1,
  assumption,
end

theorem dm1 : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  constructor,
  assume h1,
  constructor,
  assume p,
  apply h1,
  left,
  assumption,
  assume q,
  apply h1,
  right,
  assumption,
  assume h2,
  assume h3,
  cases h2 with l r,
  cases h3,
  apply l,
  assumption,
  apply r,
  assumption,  
end

open classical

theorem dm2 : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  constructor,
  assume npq,
  cases em P with p np,
  right,
  assume q,
  apply npq,
  constructor,
  assumption,
  assumption,
  left,
  assumption,
  assume npnq pq,
  cases pq with p q,
  cases npnq with np nq,
  apply np,
  exact p,
  apply nq,
  exact q,
end


theorem raa : ¬ ¬ P → P :=
begin
  assume h1,
  cases em P with p np,
  assumption,
-- either
  contradiction,
-- or
--  have f : false,
--  apply h1,
--  assumption,
--  cases f,
end


theorem nn_em : ¬ ¬ (P ∨ ¬ P) :=
begin
  assume h1,
  apply h1,
  right,
  assume np,
  apply h1,
  left,
  assumption,
end

theorem em : P ∨ ¬ P :=
begin
  apply raa,
  assume h1,
  apply h1,
  right,
  assume p,
  apply h1,
  left,
  assumption,
end

variables A B C : Type
variables PP QQ : A → Prop

 example : (∀ x : A, PP x)
   → (∀ y : A, PP y → QQ y)
   → ∀ z : A , QQ z :=
begin
  assume h1 h2 a,
  apply h2,
  apply h1,
end


example : (∀ x : A, PP x ∧ QQ x)
  ↔ (∀ x : A , PP x) ∧ (∀ x : A, QQ x) :=
begin
  constructor,
  assume h1,
  constructor,
  assume a,
  have pq : PP a ∧ QQ a,
  apply h1,
  cases pq,
  assumption,

  assume a,
  have pq : PP a ∧ QQ a,
  apply h1,
  cases pq,
  assumption,

  assume h2,
  assume a,
  cases h2 with l r,
  constructor,
  apply l,
  apply r,
end


example : (∃ x : A, PP x)
  → (∀ y : A, PP y → QQ y)
  → ∃ z : A , QQ z :=
begin
  assume h1 h2,
  cases h1 with a pa,
  existsi a,
  apply h2,
  assumption,
end


example : (∃ x : A, PP x ∨ QQ x)
              ↔ (∃ x : A , PP x) ∨ (∃ x : A, QQ x) :=
begin
  constructor,
  assume h1,
  cases h1 with a pqa,
  cases pqa,
  left,
  existsi a,
  assumption,
  right,
  existsi a,
  assumption,

  assume h2,
  cases h2,
  cases h2 with a pa,
  existsi a,
  left,
  assumption,
  cases h2 with a pa,
  existsi a,
  right,
  assumption,
end


theorem curry_pred : (∃ x : A, PP x) → R  ↔ (∀ x : A , PP x → R)  :=
begin
  constructor,
  assume h1 a,
  assume pa,
  apply h1,
  existsi a,
  assumption,

  assume h2 h3,
  cases h3 with a pa,
  apply h2,
  assumption,
end

example:  ∀ x y : A, x=y → PP y → PP x :=
begin
  
end