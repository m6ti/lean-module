
namespace l14

set_option pp.structure_projections false
open nat


#check [1,2,3]
#check [tt,ff]
#check[[0,1]]

-- check [0,tt]

#check [] --nil
#check 1 :: [2,3]

-- Haskell : -> Lean ::
-- Haskell :: -> Lean :

#check 1 :: 2 :: 3 :: []
open list


/-

Inductive list (A:Type)
| nil : list
| cons : A → list → list


[] := list
a :: as := cons a as
[1,2,3] := 1 :: 2 :: 3 :: []

inductive ℕ : type
| zero : ℕ
| succ : ℕ → ℕ 

zero ≠ succ n for all n!!!

zero ≠ succ n
succ m = succ n → m = n

-/


variables {A B C : Type}


example :∀ a : A, ∀ as : list A,
    a :: as ≠ [] :=
begin
  assume a as,
  assume h,
  contradiction,
end



example :∀ a b: A, ∀ as bs: list A,
    a :: as = b :: bs → a = b ∧ as = bs :=
begin
  assume a b as bs,
  assume h,
  constructor,
  injection h,
  injection h,
end

def tail : list A → list A
| [] := []
| (a::as) := as

example :∀ a b: A, ∀ as bs: list A,
    a :: as = b :: bs → as = bs:=
begin
  assume a b as bs h,
  apply (congr_arg tail h),

  /-
  change (tail (a :: as) = bs),
  rewrite h,
  dsimp[tail],
  refl,
  -/
end

def head : list A → A
| [] := sorry
| (a :: as) := a

-- a = b → f a = f n
example :∀ a b: A, ∀ as bs: list A,
  a :: as = b :: bs → a = b :=
begin
  -- assume a b as bs h,
  -- injection h
  sorry,
end


-- CHALLENGE : prove this without injection.


def append : list A → list A → list A
| [] bs := bs
| (a::as) bs := a :: append as bs


local notation as ++ bs := append as bs

#eval [1,2,3] ++ [4,5,6]


def append' :list A → list A → list A
| as [] := as
| as (b :: bs) := b :: (append' as bs)




def length : list A → ℕ
| [] := 0
| (a::as) := succ (length as)

#eval length [1,2,3]

example : ∀ as bs : list A,
  length (as ++ bs) = length as + length bs:=
begin
  --induction


end

/-

[] ++ as = as
as ++ [] = as
(as++bs)++cs = as++(bs++cs)

-/

theorem lneutr : ∀as : list A,
    [] ++ as = as:=
begin
  assume as,
  dsimp [(++)],
  refl,
end

theorem rneutr : ∀as : list A,
    as ++ [] = as:=
begin
  assume as,
  induction as with a as' ih,
  refl,

  dsimp [(++)],
  rewrite ih,

end


theorem assoc : ∀ as bs cs : list A,
    (as ++ bs) ++ cs = as ++ (bs ++ cs):=
begin
  assume as bs cs,
  induction as with a as' ih,
  dsimp [(++)],
  reflexivity,

  /-
  ((a :: as') ++ bs) ++ cs
  = (a :: (as' ++ bs)) ++ cs
  = a :: (as' ++ bs ++ cs)
  -/
  dsimp [(++)],
  rewrite ih,  
end

theorem comm: ∀ as bs : list A, ¬
    as ++ bs = bs ++ as :=
begin
  assume as bs h,
  
end
end l14