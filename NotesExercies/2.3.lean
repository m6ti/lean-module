variables P Q R S : Prop
theorem C: (P → Q) → (Q → R) → P → R := 
begin 
  assume p2q,
  assume q2r,
  assume p,
  apply q2r,
  apply p2q,
  exact p,
end

-- assume _ : prove an implication
-- apply _ : use an assumed implication
-- exact _ : use an assumption as it is

#print C

-- proofs are programs (functional programs)
-- propositions are types

--4065

theorem swap:
  (P->Q->R) -> (Q->P->R) :=
  begin
    assume pqr,
    assume q,
    assume p,
    apply pqr,
    exact p,
    exact q,    
  end


--  if I know h: P -> Q -> R
-- and i want to prove R
-- then O can use apply h
-- and I have 2 subgoals P and Q
-- P0 -> P1 -> ... -> Pn -> R

example : P -> Q -> P ∧ Q :=
begin
  assume p q,
  constructor,
  exact p,
  exact q,
end

theorem p : P ∧ Q -> P :=
begin
  assume h,
  cases h with p q,
  exact p,
end


theorem curry : 
  (P-> Q ->  R) ↔ (P∧Q → R) :=
begin
  constructor,
  assume pqr pq,
  apply pqr,
  cases pq with p q,
  exact p,
  cases pq with p q,
  exact q,

  assume pnqir p q,
  apply pnqir,
  constructor,
  exact p,
  exact q,
end

-- currying, haskell curry
-- (Int , Int) -> Int
-- Int -> Int -> Int

-- there are two pays to prove P ∨ Q
-- left and right

example : Q-> P ∨ Q :=
begin
  assume q,
  right,
  exact q
end 

example : (P -> R) -> (Q-> R) -> P ∨ Q -> R :=
begin
  assume pir qir poq,
  cases poq with p q,
  apply pir,
  exact p,
  apply qir,
  exact q,
end



example: false → P :=
begin
  assume pigs_can_fly,
  cases pigs_can_fly,
end

example: true :=
begin 
  constructor,
end

