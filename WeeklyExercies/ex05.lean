/-
COMP2065-IFR Exercise 05 (100)
(Natural numbers) 

Exercise 05 (Natural numbers)

The goal is to complete the proof that the natural 
numbers with addition and multiplication form a
semiring. I include the proof that addition forms a 
commutative monoid (which we have done in the lecture).

It may be advisable not to prove the theorems in 
the order I list them! Also you will need to prove 
some lemmas (auxilliary theorems).

There are 8 theorems to prove, each counts 12.5 points 
adding up to 100 if you prove them all. Don't use classical 
logic (I don't think it even helps). 

-/

set_option pp.structure_projections false

namespace mult_monoid

open nat

--we have defined +

def add : ℕ → ℕ → ℕ 
| n zero     := n
| n (succ m) := succ (add n m)

def add2 : ℕ → ℕ → ℕ 
| zero n     := n
| (succ n) m := succ (add m n)

local notation  m + n := add m n
/-
If you get an error update your lean or use:
local notation m + n := add m n 
-/


-- and have shown that it is a commutative monoid

theorem add_rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  refl,
end

theorem add_lneutr : ∀ n : ℕ, 0 + n  = n :=
begin
  assume n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end

theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  refl,
  dsimp [(+),add],
  rewrite ih,
end

lemma add_succ_lem : ∀ m n : ℕ, succ m + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  refl,
  apply congr_arg succ,
  exact ih,
end

theorem add_comm : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction m with m' ih,
  apply add_lneutr,
  calc 
    succ m' + n = succ (m' + n) : by apply add_succ_lem
    ... = succ (n + m') : by apply congr_arg succ; exact ih
    ... = n + succ m' : by reflexivity,
end

-- now we define multiplication

def mul : ℕ → ℕ → ℕ
| m 0     := 0
| m (succ n) := (mul m n) + m

local notation  m * n := mul m n


/-
If you get an error update your lean or use:
local notation m * n := mul m n 
-/

/- --- Do not add/change anything above this line (except the local notation syntax, if necessary) --- -/


-- and your task is to show that it is a commutative semiring, i.e.

-- multiplication forms a monoid



theorem mult_rneutr : ∀ n : ℕ, n * 1 = n :=
begin
  assume n,
  induction n with n' ih,
  dsimp[(*),(+)],
  refl,
  dsimp [(*)],
  rewrite add_lneutr,
end

theorem mult_lneutr : ∀ n : ℕ, 1 * n  = n :=
begin
  assume n,
  induction n with n' ih,
  dsimp[(*),(+)],
  refl,
  dsimp[(*)],
  rewrite ih,
  refl,
end

lemma  mult_distr_l_lemma1: ∀ l m n :ℕ,
 ( m + succ n) * l = m * l + succ n * l:=
begin
  assume l m n,
  induction l with l' ih,
  refl,

  dsimp[mul],
  rewrite ih,
  rewrite add_assoc,
  rewrite add_comm (succ n * l') (m + succ n),
  rewrite add_comm (succ n * l') (succ n),
  rewrite add_assoc m (succ n) (succ n * l'),
  rewrite add_assoc,
end

theorem mult_zero_l : ∀ n : ℕ , 0 * n = 0 :=
begin
  assume n,
  induction n with n' ih,
  refl,
  dsimp[mul],
  rewrite ih,
  refl,
end 


theorem mult_zero_r : ∀ n : ℕ , n * 0 = 0 :=
begin
  assume n,
  induction n with n' ih,
  refl,
  dsimp[mul],
  refl,
end

lemma mult_succ_lem : ∀ m, (succ m) = (m + 1):=
begin
  assume m,
  reflexivity,
end

lemma mult_adder : ∀ m n, (n * m + m) = (n + 1) * m :=
begin
  assume m n,
  rewrite mult_distr_l_lemma1,
  rewrite mult_lneutr,
end

lemma mult_comm_lemma1 : ∀ m n : ℕ ,m + n * m = succ n * m :=
begin
  assume m n,
  induction m with m' ih,
  rewrite mult_zero_r,
  rewrite mult_zero_r,
  reflexivity,
  
  rewrite mult_succ_lem,
  rewrite mult_succ_lem,
  rewrite add_comm,
  rewrite mult_adder,
end

theorem mult_comm :  ∀ m n : ℕ , m * n = n * m :=
begin
 assume m n,
 induction n with n' ih,
 rewrite mult_zero_l,
 rewrite mult_zero_r,
 
 rewrite mul,
 rewrite add_comm,
 rewrite ih,
 apply mult_comm_lemma1, 
end




theorem mult_distr_l :  ∀ l m n : ℕ , (m + n) * l = m * l + n * l :=
begin
  assume l m n,
  induction n with n' ih,
  dsimp[mul],
  rewrite mult_zero_l,
  refl,

  rewrite mult_distr_l_lemma1,
end

theorem mult_distr_r :  ∀ l m n : ℕ , l * (m + n) = l * m + l * n :=
begin
  assume l m n,
  induction l with l' ih,
  rewrite mult_zero_l,
  rewrite mult_zero_l,
  rewrite mult_zero_l,
  reflexivity,

  rewrite mult_comm,
  rewrite mult_distr_l,
  rewrite mult_comm,
  rewrite add_comm,
  rewrite mult_comm,
  rewrite add_comm,
end


lemma lemma1: ∀ l m n':ℕ, (l * (m * n')) + (l * m)  =  (l * (m * n' + m)):=
begin
  assume l m n',
  induction m with m' ih,
  dsimp[mul],
  refl,
  rewrite mult_distr_r,
end


theorem mult_assoc : ∀ l m n : ℕ , (l * m) * n = l * (m * n) :=
begin
  assume l m n,
  induction n with n' ih,
  dsimp [mul],
  refl,
  dsimp[mul],
  rewrite ih,
  rewrite lemma1,
end

-- distributivity laws


-- commutativity



/- --- Do not add/change anything below this line --- -/
end mult_monoid
