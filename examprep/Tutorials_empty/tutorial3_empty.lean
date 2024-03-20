/-
COMP2065 Tutorial 3
-/

/-
A proposition is a statement that we may be able to prove.
E.g. Germany is in Europe, 9 > 3, 6 is an odd number

A predicate expresses properties of objects. It depends upon variables.
E.g. in_Europe : Country → Prop (in_Europe Germany holds)
     >3 : ℕ → Prop (>3 9 holds)
     is_odd : ℕ → Prop (the negation of is_odd 6 holds)

Predicate logic extends propositional logic by adding two 
quantifiers:
* universal quantification: ∀ x : A, PP x
* existential quantification: ∃ x : A, PP x
for A : Type, PP : A → Prop
-/

variable P : Prop
variables A B : Type -- types e.g. ℕ, Bool
variables PP QQ : A → Prop -- predicates e.g. is_odd : ℕ → Prop
variable R : A → B → Prop -- relations e.g. is_greater_than : ℕ → ℕ → Prop

open classical

theorem raa : ¬ ¬ P → P := 
begin
  assume nnp,
  cases (em P) with p np,
    exact p,
    have f : false,
      apply nnp,
      exact np,
    cases f,
end

------------------------------------------------------------------------------
-- PART I: Formal Definitions

-- Example 1 (proposition) - Every car has four wheels

constant Car : Type

-- has_four_wheels c means c has four wheels
constant has_four_wheels : Car → Prop

def every_car_has_four_wheels : Prop 
  := ∀ c: Car, has_four_wheels c

-- Example 2 (proposition) - There is at least one natural number
-- that is both even and prime

constant Nat : Type

-- even n means n is even; prime n means n is prime
constants even prime : Nat → Prop

def nat_even_prime : Prop 
  := ∃k:Nat, (even k) ∧ (prime k)  

-- Example 3 (relation) - x is the father-in-law of y

constant People : Type

-- Male x means x is male; Female x means x is female
constants Male Female : People → Prop

-- Parent x y means x is the parent of y
constant Parent : People → People → Prop 

-- Married x y means x is married to y
constant Married : People → People → Prop

def Father (x y : People) : Prop 
  := Parent x y ∧ Male x 

def FatherInLaw (x y : People) : Prop
  := ∃ z: People, Married x z ∧ Parent z y  

-- Example 4 (proposition) - Everyone has exactly one biological mother

-- Mother x y means x is the mother of y
constant Mother : People → People → Prop

def exactly_one_mother : Prop 
  := ∀ y : People, ∃ x : People, Mother x y ∧ 
                  (∀ z: People, Mother z y → x = z)

------------------------------------------------------------------------------
-- PART II: Using ∀ and ∃ Quantifiers and Equality

-- To prove a (∀ x : X, PP x), we use `assume`
-- To use a (∀ x : X, PP x), we use `apply`

theorem comm_all : (∀ a : A, ∀ b : B, R a b) → (∀ b : B, ∀ a : A, R a b) :=
begin
  assume a b a',
  apply a,
end  

-- To prove a (∃ x : X, PP x), we use `existsi`
-- To use a (∃ x : X, PP x), we use `cases`

theorem comm_exists : (∃ a : A, (∃ b : B, R a b)) → (∃ b : B, (∃ a : A, R a b)) :=
begin
  assume a,
  cases a with a' h,
  cases h with b h2,
  existsi b,
  existsi a',
  exact h2,
end  

-- To prove _=_, we use `reflexivity` (this proves x=x)
-- To use _=_, we use `rewrite`
-- x ≠ y is defined as ¬ (x = y) i.e. (x = y) → false

theorem sym_neq : ∀ x y : A, x≠y → y≠x :=
begin
  assume x y h,
  assume yx,
  rewrite yx at h,
  contradiction,
end  

theorem trans_eq : ∀ x y z : A, x = y ∧ y = z → x = z :=
begin
  assume x y z h,
  cases h with l r,
  rewrite l,
  rewrite r,
end

------------------------------------------------------------------------------
-- PART III: Examples

/-
3 possible cases: 
* A) provable intuitionistically
* B) provable classically
* C) not provable 
-/  

theorem all_nex : (∀ a : A, PP a) → (¬ ∃ a : A, ¬ PP a) :=
begin
  assume h neg,
  cases neg with a npa,
  apply npa,
  apply h,
end

theorem nex_all : (¬ ∃ a : A, ¬ PP a) → (∀ a : A, PP a) :=
begin
  --provable classically.
  assume h a,
  apply raa,
  assume npa,
  apply h,
  existsi a,
  exact npa,
end

variable S : A → A → Prop -- new relation

theorem S_trans : (∀ a a' : A, S a a' → S a' a) :=
begin
  -- Not provable
  sorry,
end

theorem dm2_pred : ¬ (∀ x : A, PP x) ↔ (∃ x : A, ¬ PP x) :=
begin
  constructor,
  assume h1,
  apply raa,
  assume npa,
  apply h1,
  assume x,
  apply raa,
  assume npx,
  apply npa,
  existsi x,
  exact npx,

  assume h2,
  assume all,
  cases h2 with a npa,
  apply npa,
  apply all,
end 

-- Optional

theorem ex_nall : (∃ a : A, PP a) → (¬ ∀ a : A, ¬ PP a) :=
begin
  assume h1,
  assume h2,
  cases h1 with a pa,
  have g: ∃ x: A, ¬ PP a,
  existsi a,
  apply h2,
  cases g,
  contradiction,
end

theorem ind_of_ids: ∀ x y : A, x = y → (PP x ↔ PP y) :=
begin
  assume x y h,
  rewrite h,
end
