/-
Lecture 12: Algebra and order
-/

--import tactic

namespace l12
set_option pp.structure_projections false
open nat


/-theorem binom : ∀ x y : ℕ, (x + y)^2 = x^2 + 2*x*y + y^2 :=
begin
assume x y,
ring,
end-/


--ORDER
def le (m n : ℕ) : Prop :=
∃ k : ℕ, k + m = n

def le' (m n : ℕ) : Prop :=
∃ k : ℕ, k * m = n

local notation m ≤ n := le m n

example : 2 ≤ 3 :=
begin
dsimp[(≤)],
existsi 1,
reflexivity,
end

example : ¬ (3 ≤ 2) :=
begin
assume h,
dsimp[(≤)] at h,
cases h with k hh,
have h2 : k+2 = 1,
injection hh,
have h3 : k+1 = 0,
injection h2,
contradiction,
end



-- what are properties of ≤ (order theory)
-- A relation that has all these is called partial order
-- reflexivity

/-theorem le_refl : ∀ n : ℕ, n ≤ n :=
begin
assume n,
dsimp[(≤)],
existsi 0,
ring,
end-/

--transitivity
/-theorem le_trans : ∀ l m n : ℕ, l ≤ m → m ≤ n → l ≤ n :=
begin
dsimp[(≤)],
assume l m n lm mn,
cases lm with k h,
cases mn with k' hh,
existsi (k + k'),
rewrite← hh,
rewrite← h,
ring,
end-/

--anti-symmetry
theorem anti_sym : ∀ m n : ℕ, m ≤ n → n ≤ m → m = n :=
begin
assume m n,
sorry,
end

def lt (m n : ℕ) : Prop := m + 1 ≤ n

local notation x < y := lt x y

/-
∀n : ℕ, ¬ (n ⋖ n)
∀ l m n : ℕ, l ⋖ m → m ⋖ n → l ⋖ n
∀ m n : ℕ, m ⋖ n → n ⋖ m → false


⋖ is well founded

transitive + well founded = well order
-/

end l12