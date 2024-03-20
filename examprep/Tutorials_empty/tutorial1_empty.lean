/-
COMP2065 Tutorial 1
-/

/-
Two ways to use Lean:
* Web interface providing a Javascript version of Lean. 
* Install and run it natively on your computer.

We will be using Lean 3.

Link for installing Lean 3: https://leanprover-community.github.io/lean3/
-/

variables P Q R : Prop

---------------------------------------------------------------------------
-- PART I: TACTICS
-- Tactics are commands Lean understands, which we use to describe how to 
-- build a specific proof.

-- `assume h` - used to assume a premise to prove an implication
-- `exact h` - used when there is an assumption that exactly matches the goal

theorem reflexivity : P → P :=
begin
  assume p,
  exact p,
end

-- `apply t` - uses an implication; if we assume t : P → Q and our goal is Q,
--             we 'apply t' to reduce our goal to P

theorem swap : (P → Q → R) → Q → P → R :=
begin
  assume h1 h2 h3,
  apply h1,
  exact h3,
  exact h2,
end  

-- `constructor` - used to prove conjunction (∧), splits goal P ∧ Q into 2
--                 goals P and Q

theorem and_intro : P → Q → (P ∧ Q) :=
begin
  assume p q,
  constructor,
  assumption,
  assumption,
end   

-- `cases p` - splits assumption P ∧ Q into assumptions P and Q which are
--             added to the current goal;
--             splits assumption P ∨ Q into assumption P in one subgoal
--             and assumption Q in another subgoal

theorem and_elim : P ∧ Q → P :=
begin
  assume h,
  cases h with l r,
  exact l,
end  

theorem or_elim : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  assume h1 h2 h3,
  cases h3,
  apply h1,
  assumption,
  apply h2,
  assumption,
end  

-- `left` & `right` - used to prove disjunction (∨)

theorem comm_or : P ∨ Q → Q ∨ P :=
begin
  assume h1,
  cases h1,
  right,
  assumption,
  left,
  assumption,
end  

---------------------------------------------------------------------------
-- PART II: LOGICAL CONNECTIVES

-- Negation is defined as ¬ P := P → false

theorem contrapositive : (P → Q) → (¬ Q → ¬ P) :=
begin
  assume h1 h2 np,
  apply h2,
  apply h1,
  exact np,
end

-- Equivalence is defined as P ↔ Q := (P → Q) ∧ (Q → P)

theorem distr : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
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

  assume h2,
  cases h2,
  constructor,
  cases h2,
  assumption,
  cases h2,
  left,
  assumption,
  cases h2 with l r,
  constructor,
  assumption,
  right,
  assumption,
end  

---------------------------------------------------------------------------
-- PART III: MISC PROOFS

-- Eliminating false using cases 

theorem ex_falso_quod_libet : false → P :=
begin
  assume h,
  contradiction,
end 

-- Constructing truth

theorem truth : P → true :=
begin
  assume p,
  constructor,
end  

-- Other proofs

theorem negate_p : ¬ P → P → Q :=
begin
  assume h1 h2,
  contradiction,
end

theorem too_many_negations : ¬ ¬ ¬ P → ¬ P :=
begin
  assume h1,
  assume h2,
  apply h1,
  assume h3,
  apply h3,
  exact h2,
end

---------------------------------------------------------------------------
