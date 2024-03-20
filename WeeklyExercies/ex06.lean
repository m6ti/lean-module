/-
COMP2065-IFR Exercise 06 (100)
(Less or equal (≤)) 

Exercise 06

The goal is to prove some properties of ≤ on the natural numbers:

6a) ≤ is antisymmetric (50%)
6b) ≤ is decidable (50%)

-/
set_option pp.structure_projections false

namespace ex06 
 
open nat

/- from the lecture: 
  defn of + and proof that it is a commutative monoid.
-/

def add : ℕ → ℕ → ℕ 
| n zero := n
| n (succ m) := succ (add n m)

local notation m + n := add m n
/-
If you get an error update your lean or use:
local notation m + n := add m n 
-/

theorem lneutr : ∀ n : ℕ, 0 + n = n :=
begin
 assume n,
 induction n with n' ih,
 reflexivity,
 dsimp [(+)],
 rewrite ih,
end

theorem rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  dsimp [(+),add],
  reflexivity
end

theorem assoc : ∀ l m n : ℕ, 
    (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  dsimp [(+),add],
  reflexivity,
  dsimp [(+),add],
  rewrite ih,
end   

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

theorem comm : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction n with n' ih,
  dsimp [(+),add],
  rewrite lneutr,
  dsimp [(+),add],
  rewrite add_succ,
  rewrite ih,
end

-- from the lecture : definition of ≤ .

def le(m n : ℕ) : Prop :=
  ∃ k : ℕ , k + m = n

local notation x ≤ y := le x y
/-
If you get an error update your lean or use:
local notation x ≤ y := le x y 
-/

-- end of lecture material

/- --- Do not add/change anything above this line (except the `local notation` syntax, if necessary) --- -/
lemma refl_eq : ∀ m n : ℕ, m = n ↔ n = m:=
begin
  assume m n,
  constructor,
  assume h,
  rewrite h,
  assume h2,
  rewrite h2,
end
lemma succ_adder : ∀ x y : ℕ , x = y ↔ succ x = succ y :=
begin
  assume x y,
  constructor,
  assume h1,
  rewrite congr_arg succ,
  assumption,
  assume h2,
  induction y with y' ih,
  dsimp [add] at h2,
  cases x,
  refl,
  --WOW
  injection h2,
  injection h2,
end

/- 6a) Prove that ≤ is antisymmetric. (50%)
  Hint: it may be a good idea to prove some lemmas.-/
lemma eq_sym1: ∀ x y : ℕ, (∃ (k : ℕ), k + x = y) ∧ (∃ (k : ℕ), k + y = x) → x = y:=
begin
  assume x,
  induction x with x' ih,
  assume y,
  assume h,
  cases h with l r,
  cases r with n ih,
  cases n,
  rewrite lneutr at ih,
  rewrite refl_eq,
  assumption,

  have f:false,
  cases y,
  contradiction,
  contradiction,
  cases f,

  assume y,
  assume h,
  cases y,
  cases h with l r,
  have f: false,
  cases l with n ij,
  cases n,
  contradiction,
  contradiction,
  cases f,
  apply congr_arg succ,
  apply ih,
  cases h with l r,
  cases l with lx hx,
  cases r with lx' hx',
  constructor,
  cases lx,
  cases lx',
  existsi 0,
  rewrite lneutr at hx,
  rewrite lneutr,
  injection hx,
  existsi 0,
  rewrite lneutr at hx,
  rewrite lneutr,
  injection hx,
  existsi succ lx,
  injection hx,
  existsi lx',
  injection hx',
  
  /-
  induction x with x' ih,
  assume y h,
  cases h with h1 h2,

  cases y,
  cases h1 with n h3,
  cases n,
  refl,
  refl,
  cases y,
  cases h2 with n h4,
  cases h1 with n h5,
  have f:false,
  contradiction,
  cases f,
  have f:false,
  cases h2,
  contradiction,
  cases f,

  assume y h,
  cases y,
  cases h with h1 h2,
  cases h1 with n h3,
  cases n,
  rewrite<- h3,
  rewrite lneutr,
  have f:false,
  contradiction,
  cases f,
  apply congr_arg succ,
  apply ih,
  cases h with l r,
  cases l with n h1,
  cases r with n h2,

  constructor,
  cases n,

  existsi 0,
  rewrite lneutr,
  rewrite lneutr at h2,
  injection h1,
  cases n,
  rewrite lneutr at h1,
  injection h1,
  rewrite refl_eq,
  injection h2,

  existsi n,
  injection h1,
  
  cases n,
  existsi 0,
  rewrite lneutr,
  rewrite lneutr at h2,
  injection h2,



  existsi succ n_1,
  injection h2,-/
end







theorem anti_sym : ∀ x y : ℕ , x ≤ y → y ≤ x → x = y :=
begin
  assume x y h1,
  dsimp[(≤)] at h1, 
  assume h2,
  dsimp[(≤)] at h2,

  apply eq_sym1,
  constructor,
  assumption,
  assumption,
end


/-
6b) Show that ≤ is decidable, by defining a function returning 
a boolean (10%).

You should define leb in such a way that you can prove
  ∀ m n : ℕ, m ≤ n ↔ leb m n = tt
-/

def leb : ℕ → ℕ → bool
 | zero _ := tt
 | (succ n) zero := ff
 | (succ n) (succ m) := leb n m

--#eval leb 2 5
/- Now, show that leb computes ≤, i.e. that
 your definition of leb satisfies its specification. (40%) -/

theorem leb_ok : 
  ∀ m n : ℕ, m ≤ n ↔ leb m n = tt :=
begin
  assume m,
  induction m with m' ih,
  assume n,  
  constructor,
  rewrite [(≤)],
  assume h1,
  cases n,
  reflexivity,
  reflexivity,

  assume h2,
  rewrite [(≤)],
  cases n,
  existsi 0,
  reflexivity,
  existsi succ n,
  reflexivity,
  
  assume n,
  constructor,
  dsimp [(≤)],
  dsimp [(≤)] at ih,
  assume h,
  cases h with k ih',
  rewrite<- ih',
  change leb (succ m') (succ(k +  m')) = tt,
  rewrite leb,
  rewrite<- ih,
  cases k,
  existsi 0,
  reflexivity,
  existsi succ k,
  reflexivity,

  assume h2,
  dsimp [(≤)] at ih,
  dsimp [(≤)],
  
  cases m',
  cases n,
  contradiction,
  rewrite leb at h2,
  rewrite<- ih at h2,
  existsi n,
  reflexivity,

  cases n,
  contradiction,
  rewrite leb at h2,
  rewrite<- ih at h2,
  cases h2 with n' ih',
  rewrite<- ih',
  rewrite add,
  existsi n',
  reflexivity,
end


/-
  cases m',
  cases n,
  cases h with n ih',
  contradiction,
  rewrite leb,
  cases n,
  reflexivity,
  reflexivity,
-/


/- --- Do not add/change anything below this line --- -/
end ex06