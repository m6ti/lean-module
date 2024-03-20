/-
Lean class test for COMP2065 
(Introduction to Formal Reasoning)

Replace all the "sorry"s below by Lean proofs,
using only the tactics introduced in the 
lectures and only in the way they were taught.

-/

set_option pp.structure_projections false

namespace test

open nat list classical

variables P Q R : Prop
/- --- Do not change or delete anything above this line --- -/

theorem e01 : P ∧ (Q ∧ R) → P ∧ (Q ∧ R) := 
begin
  assume h,
  assumption,
end

theorem e02 : P ∨ Q → Q ∨ P :=
begin
  assume h,
  cases h,
  right,
  assumption,
  left,
  assumption,
end

theorem e03 : (P → Q) → ¬ Q → ¬ P :=
begin
  assume h1,
  assume h2,
  assume p,
  apply h2,
  apply h1,
  assumption,
end

theorem e04 : ¬ ¬ (P ∧ Q) → ¬ ¬ P :=
begin
  assume h,
  assume h2,
  apply h,
  assume h3,
  apply h2,
  cases h3,
  assumption,
end

-- Do not change/remove --
variable {A : Type}
variables PP QQ : A → Prop
-- /Do not change/remove --

theorem e05 : (∃ x : A, true)
  → (∀ x : A, PP x ∧ P) → P :=
begin
  assume h1 h2,
  cases h1 with a t,
  have g:  ∃ (x : A), PP x ∧ P,
  existsi a,
  apply h2,
  cases g,
  cases g_h,
  assumption,
end

theorem e06 : ∀ x : A,
  (∀ y : A, x = y → PP y) ↔ PP x :=
begin
  assume a,
  constructor,
  assume h1,
  apply h1,
  reflexivity,

  assume h2,
  assume y,
  assume h3,
  rewrite<- h3,
  assumption,
end

-- Do not change/remove --
def bnot : bool → bool
| tt := ff
| ff := tt 
prefix `!`:90 := bnot
-- /Do not change/remove --

theorem e07 : ∀ x : bool, ∃y : bool,
  ! y = x :=
begin
  assume h1,
  cases h1,
  existsi tt,
  dsimp [bnot],
  reflexivity,

  existsi ff,
  dsimp[bnot],
  reflexivity,
end

-- Do not change/remove --
def add : ℕ → ℕ → ℕ 
| n zero := n
| n (succ m) := succ (add n m)
-- /Do not change/remove --


local notation m + n := add m n
/-
If you get an error, please use this line instead:
local notation m + n := add m n 
-/

-- Do not change/remove --
def double : ℕ → ℕ
| zero := 0
| (succ n) := succ (succ (double n))

lemma add_succ : ∀ m n : ℕ,
  (succ m) + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  dsimp [(+),add],
  reflexivity,
  dsimp [(+),add],
  rewrite ih,
end
-- /Do not change/remove --

theorem e08 : ∀n : ℕ, n + n = double n:=
begin
  assume n,
  induction n with n ih,
  dsimp [double, (+)],
  reflexivity,

  dsimp[double],
  rewrite add_succ,
  dsimp[(+)],
  rewrite ih,
end


theorem e09 : ∀ l : list A, l = [] ∨
    ∃ a : A, ∃ l' : list A, l = a :: l' :=
begin
  assume l,
  induction l with a as ih,
  left,
  reflexivity,

  right,
  existsi a,
  existsi as,
  reflexivity,
end

-- Do not change/remove --
def append : list A → list A → list A
| [] bs := bs
| (a :: as) bs := a :: (append as bs)
-- /Do not change/remove --

local notation as ++ bs := append as bs
/-
If you get an error, please use this line instead:
local notation as ++ bs := append as bs 
-/


theorem e10 : ∀ l : list A, l = [] ∨
  ∃ a : A, ∃ l':list A, l = l'++[a] :=
begin
  assume l,
  induction l with a as ih,
  left,
  reflexivity,

  cases ih,
  right,
  rewrite ih,
  existsi a,
  existsi as,
  rewrite ih,  
  reflexivity,


  right,
  cases ih with a ih2,
  cases ih2 with as ih3,
  existsi a,
  existsi as,
  rewrite<- ih3,
  
end


/- --- Do not change or delete anything below this line --- -/
end test