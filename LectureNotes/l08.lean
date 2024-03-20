/-
  Lecture 08: Predicate Logic
-/

set_option pp.structure_projections false

variables P Q R : Prop
variables A B C : Type
variables PP QQ : A → Prop
variables RR : A → A → Prop

/-

curry
P∧Q → R ↔ P → Q → R

∀ ~ →
∃ ~ ∧

-/

-- A = Students, PP x = x is clever
-- R = the lecturer is happy.

example :  (∃ x : A, PP x) → R ↔ (∀ x : A, PP x → R):=
begin
  constructor,
  assume h a pa,
  apply h,
  existsi a,
  assumption,
  assume h pp,
  -- insert this before apply h,
  cases pp with a pa,
  apply h,
  -- uhoh... ?m_1 happens... 2 assumptions. PP x and A as seperate goals
  -- except we haven't given a name to element x.
  /-
  cases pp with a pa,
  apply pa,
  -/
  apply pa,
  
  -- strange tautology
end

/-
  ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q

  ∀ ~ ∧ 
  ∃ ~ ∨ 

  ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x

-/

example : ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x :=
begin
  constructor,
  assume pp a,
  assume ppa,
  apply pp,
  existsi a,
  exact ppa,

  assume h ppx,
  cases ppx with p pa,
  apply h,
  apply pa,
end

-- nice one.

open classical 

-- second de morgan -> ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q

-- principle of the excluded middle. 

theorem raa : ¬ ¬ P → P:=
begin 
  assume nnp,
  have pnp : P ∨ ¬ P,
  
  apply em,

  cases pnp,

  assumption,
  have f: false,
  apply nnp, 
  assumption,

  cases f,
end

example : ¬(∀ x: A, PP x) ↔ ∃ x : A, ¬ (PP x):=
begin
  constructor,
  assume h,
  -- need an element, but we dont know one...
  apply raa,
  -- 'if there isnt anybody, then it isnt possible'
  assume npx,
  apply h,
  assume a,
  apply raa,
  assume nppa,
  apply npx,
  existsi a,
  assumption,

  assume h ppx,
  cases h with a nppa,
  apply nppa,
  apply ppx,
end 

/-
  (∀ x : A, PP x ∧ QQ) ↔ (∀ x: A, PP x) ∧ (∀ x : A, QQ x)

  (∃ x : A, PP x ∨ QQ) ↔ (∃ x: A, PP x) ∨ (∃ x : A, QQ x)

  bool = {tt, ff

  inductive bool : Type
  | tt: bool
  | ff: bool

-/

variable SS : bool → Prop

example: (∀ x : bool, SS x) ↔ SS tt ∧ SS ff:=
begin
  constructor,
  assume h,
  constructor,
  apply h,
  apply h,
  assume h x,
  cases h with st sf,
  cases x,
  apply sf,
  apply st,
end

example: (∃ x : A, PP x ∨  QQ x) ↔ (∃ x: A, PP x) ∨ (∃ x : A, QQ x):=
begin

end 