/-
COMP2065 Tutorial 7
-/

namespace lists

open nat list
set_option pp.structure_projections false
variables {A B C : Type}

-- From lecture notes

theorem add_rneutr : ∀ n : ℕ, n + 0 = n := sorry
theorem add_lneutr : ∀ n : ℕ, 0 + n  = n := sorry
theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) := sorry
theorem add_succ_lem : ∀ m n : ℕ, (succ m) + n = succ (m + n) := sorry 
theorem add_comm : ∀ m n : ℕ , m + n = n + m := sorry

------------------------------------------------------------
-- Part I: Definition of lists

/-
inductive list (A : Type)
| nil  : list
| cons : A → list → list

nil is denoted by []
cons a as is denoted by a :: as
[a] is shorthand for a :: []
-/

-- Injectivity of constructor `cons`

theorem cons_inj : ∀ a b : A, ∀ as bs : list A,
                   a :: as = b :: bs → a = b ∧ as = bs :=
begin
  assume  a b as bs eq,
  constructor,
  injection eq,
  injection eq,
end

------------------------------------------------------------
-- Part II: Some functions on lists: length, append, snoc

-- Length

def length : list A → ℕ
| []        := 0
| (a :: as) := succ (length as) 

--#eval (length ['a','b','c'])

-- Append 

def append : list A → list A → list A
| []       l := l
| (h :: s) t := h :: (append s t)

local notation  l₁ ` ++ ` l₂ := append l₁ l₂
-- If you get an error, replace with:
-- local notation l₁ ` ++ ` l₂ := append l₁ l₂

--#eval (['h','e'] ++ ['l','l','o'])

theorem app_lneutr : ∀ l : list A, [] ++ l = l := sorry
theorem app_rneutr : ∀ l : list A, l ++ [] = l := sorry
theorem assoc : ∀ as bs cs : list A, 
                (as ++ bs) ++ cs = as ++ (bs ++ cs) := sorry

theorem append_length : ∀ as bs : list A,
  length (as ++ bs) = length as + length bs :=
begin
  assume as bs,
  induction as with a as' ih,
  dsimp [append,length],
  rewrite add_lneutr,
  
  dsimp[append,length],
  rewrite ih,
  rewrite add_succ_lem,
end

-- Snoc
--cons adds element to the front of the list, snoc adds to end!

def snoc : list A → A → list A
| []        a := [a]
| (a :: as) b := a :: (snoc as b)

--#eval (snoc [3,4,5] 0)

theorem snoc_append : ∀ as : list A, ∀ a : A, 
                      snoc as a = as ++ [a] :=
begin
  assume as,
  induction as with a' as' ih,

  assume a,
  dsimp [(++),snoc],
  refl,

  assume a,
  dsimp [(++), snoc],
  rewrite ih,

end

------------------------------------------------------------
-- Part III: Reverse

-- Rev

def rev : list A → list A 
| []        := []
| (a :: as) := snoc (rev as) a

/-
rev [3,1,5] = rev (3 :: 1 :: 5 :: [])
            = snoc ((rev 1 :: 5 :: [])) 3
            = snoc ( snoc (rev (5 :: [])) 1)  3
            = snoc ( snoc ( snoc ([]) 5 ) 1 ) 3
            = snoc ( snoc ( 5 :: [] ) 1 ) 3
            = snoc ( 5 :: snoc [] 1) 3
            = snoc (5 :: 1 :: [] ) 3
            = 5 :: snoc ( 1 :: []) 3
            = 5 :: 1 :: snoc [] 3
            = 5 :: 1 :: 3 :: []
            = [5,1,3] 
-/

-- Fastrev

def revaux : list A → list A → list A
| []        bs := bs
| (a :: as) bs := revaux as (a :: bs)

#eval revaux [1,2,3] [4]

def fastrev (l : list A) : list A := revaux l []

/-
fastrev [3,1,5] 
= fastrev (3 :: 1 :: 5 :: [])
= revaux (3 :: 1 :: 5 :: []) []
= revaux (1 :: 5 :: []) (3 :: [])
= revaux (5 :: []) (1 :: 3 :: [])
= revaux [] (5 :: 1 :: 3 :: [])
= 5 :: 1 :: 3 :: []
= [5,1,3]
-/


/-
 l= [7,8,9]
 m= [1,2]

 rev l ++ rev m = [9,8,7] ++ [2,1] = [9,8,7,2,1]
 rev (m ++ l)  = rev [1,2,7,8,9] = [9,8,7,2,1]

-/
lemma rev_append_lem :
    ∀ ls as: list A, ∀a: A,  
      ls ++ snoc as a = snoc (ls ++ as) a :=
begin
  assume ls,
  induction ls with l' ls' ih,
  assume as a,
  dsimp [(++)],
  refl,


--REWRITE ON OWN
  assume as a,
  dsimp [(++)],
  rewrite ih,
  dsimp [snoc],
  refl,
end

theorem rev_append : ∀ l m : list A, 
                     rev l ++ rev m = rev (m ++ l) :=
begin
  assume l m,
  induction m with a as ih,
  dsimp [rev,(++)],
  rewrite app_rneutr,

  dsimp [rev,(++)],
  rewrite<- ih,
  rewrite rev_append_lem,
end

def map_list : (A → B) → list A → list B
| f []        := []
| f (a :: as) := f a :: map_list f as

/-
Assume f : A → B
 
list A    map_list f -->   list B
  |                           |
  rev                        rev
  |                           |
  ↓                           ↓ 
list A    map_list f -->   list B             


-/

lemma nat_rev_lem :∀ f: A→B, ∀as: list A, ∀ a:A,  map_list f (snoc as a) = snoc (map_list f as) (f a):=
begin
  sorry,
end

#eval (map_list (*2) [2,3,4])

theorem nat_rev : ∀ f : A → B, ∀ l : list A,
                  map_list f (rev l) = rev (map_list f l) := 
begin
  assume f l,
  induction l with a as ih,
  dsimp[rev,map_list],
  refl,

  dsimp [rev,map_list],
  rewrite <- ih,
  rewrite nat_rev_lem,
end

lemma rev_idempotent :∀as: list A, as = rev(rev(as)):=
begin
  sorry,
end

theorem rev_app : ∀ as bs : list A, rev as ++ bs = rev (rev bs ++ as) :=
begin 
  assume as,
  induction as with a' as' ih,
  assume bs,
  dsimp [rev , (++)],
  rewrite app_rneutr,
  rewrite<- rev_idempotent bs,
  
  assume bs,
  dsimp [rev],
  rewrite snoc_append,
  rewrite assoc,
  dsimp [(++)],
  rewrite ih,
  dsimp [rev],
  apply congr_arg rev,
  rewrite snoc_append,
  rewrite assoc,
  dsimp [(++)],
  refl,
  /-rewrite ih,
  dsimp [rev,snoc,(++)],
  rewrite snoc_append,
  rewrite assoc,
  dsimp [(++)],-/
  
end

/-
Notes:

1. `rev` is defined using the helper function `snoc`. So 
   proofs on `rev` will usually require a helper lemma 
   on `snoc`.

2. Remember that in some cases you can obtain a stronger 
   inductive hypothesis if you apply induction earlier.
-/

end lists
