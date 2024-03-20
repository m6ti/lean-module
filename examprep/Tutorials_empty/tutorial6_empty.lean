/-
COMP2065 Tutorial 6
-/

set_option pp.structure_projections false

namespace morenaturals

open nat

------------------------------------------------------------
-- PART I: Minimum

-- definition of minimum
def min : ℕ → ℕ → ℕ 
| 0 n := 0
| (succ n) 0 := 0
| (succ n) (succ m) := succ (min n m)

theorem min_assoc : 
  ∀ l m n : ℕ, min (min l m) n = min l (min m n) :=
begin
  assume l,
  induction l with l' ih,
  assume  m n,
  reflexivity,

  assume m n,
  cases m,
  dsimp [min],
  reflexivity,

  dsimp [min],
  cases n,
  reflexivity,

  dsimp [min],
  apply congr_arg succ,
  apply ih,
end

------------------------------------------------------------
-- PART II: Less than or equal to

-- definition of +
def add : ℕ → ℕ → ℕ 
| n zero := n 
| n (succ m) := succ (add n m)

-- local notation (name := add) m ` + ` n := add m n
-- If you get an error, replace with:
local notation m ` + ` n := add m n

-- definition of ≤ 
def le (m n : ℕ) : Prop :=
  ∃ k : ℕ , k + m = n

-- local notation (name := le) x ` ≤ ` y := le x y
-- If you get an error, replace with:
local notation x ` ≤ ` y := le x y

lemma add_rneutr : ∀ a : ℕ, a + 0 = a := sorry
lemma add_lneutr : ∀ a : ℕ, 0 + a = a := sorry 
lemma add_assoc : ∀ a b c : ℕ, (a + b) + c = a + (b + c) := sorry
lemma add_comm : ∀ a b : ℕ , a + b = b + a := sorry


theorem le_cancel_succ : ∀ m n : ℕ, succ m ≤ succ n → m ≤ n :=
begin
  assume m n,
  dsimp [le],
  assume h,
  cases h with n h',
  existsi n,
  dsimp [add] at h',
  injection h',
end

lemma add_lem : ∀ x y : ℕ, x + y = y → x = 0 :=
begin
  assume x y,
  induction y with y' ih,
  assume h,
  rewrite add_rneutr at h,
  exact h,

  assume h,
  dsimp [add] at h,
  apply ih,
  injection h,

end

lemma le_min_lem : ∀ k m : ℕ, min m (k + m) = m :=
begin
  assume k m,
  induction m with m' ih,
  reflexivity,

  dsimp [add,min],
  apply congr_arg succ,
  exact ih,
end

theorem le_min : ∀ m n : ℕ, m ≤ n → min m n = m :=
begin
  assume m n l,
  dsimp [le] at l,
  cases l with k eqk,
  rewrite<- eqk,
  apply le_min_lem,
end

theorem lower_bound : ∀ m n : ℕ, min m n ≤ m :=
begin
  assume m,
  induction m with m' ih,
  dsimp [le],
  assume n,
  existsi 0,
  refl,

  assume n,
  cases n,
  dsimp [min,le],
  existsi (succ m'),
  reflexivity,
  
  dsimp [min],
  dsimp [le] at ih,
  dsimp [le,add],
  have h : ∃ (k : ℕ), k + min m' n = m',
  apply ih,

  cases h with n' h2,
  existsi n',
  rewrite h2,
end

end morenaturals