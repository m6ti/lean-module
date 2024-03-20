/-
COMP2065-IFR Exercise 07
(fast reverse) 

Our goal is to prove that fast reverse computes the same function
as reverse.

-/

open list
set_option pp.structure_projections false
variables {A B C : Type}
namespace revDefn

/- 
In the lecture we have introduced the function reverse
(and the auxilliary function snoc)
-/

def snoc : list A → A → list A
| [] a := [a]
| (a :: as) b := a :: (snoc as b)

def rev : list A → list A 
| [] := []
| (a :: as) := snoc (rev as) a

/- 
Our implementation of rev is inefficient: it has O(n^2) complexity.
The definition below (called fastrev) is efficient, having only O(n) complexity.
It uses an auxillary function revaux which accumulates the reversed 
list in a 2nd variable.
-/

def revaux : list A → list A → list A
| [] bs := bs
| (a :: as) bs := revaux as (a :: bs)

def fastrev (l : list A) : list A
  := revaux l []

#reduce fastrev [1,2,3]


end revDefn

namespace ex07
open revDefn
/- --- Do not add/change anything above this line --- -/

/-
However we would like to show that fast rev and rev do the same thing.

You'll need to establish a lemma about revaux (hint: try writing
down a precise specification of what revaux does).

You may use the fact that lists with ++ form a monoid 
(just copy the proofs from the lecture).
-/
def append : list A → list A → list A
| []       l := l
| (h :: s) t := h :: (append s t)

local notation  l₁ ` ++ ` l₂ := append l₁ l₂

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


#eval revaux [1,2,3] [6] 

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

lemma snoc_lem : ∀ a: A, ∀ as bs: list A,
  snoc as a ++ bs = as ++ a :: bs :=
begin
  assume a as,
  induction as with a' as' ih,
  assume bs,
  reflexivity,

  assume bs,
  rewrite snoc_append,
  dsimp [(++)],
  rewrite assoc,
  dsimp [(++)],
  reflexivity,
end 

lemma revaux_lem : ∀ as bs :list A, revaux as bs = rev as ++ bs:=
begin
  assume as,
  induction as with a as' ih,
  assume bs,
  reflexivity,

  assume bs,
  dsimp [revaux],
  dsimp [rev],
  rewrite ih,
  rewrite snoc_lem,
end


theorem fastrev_thm : ∀ as : list A , fastrev as = rev as :=
begin
  assume as,
  induction as with a as' ih,

  dsimp [rev,fastrev,revaux],
  refl,


  dsimp [fastrev] at ih,
  dsimp [fastrev,revaux,rev],
  rewrite revaux_lem,
  rewrite snoc_append,

  /-

  dsimp [rev,fastrev,revaux,snoc,snoc_append],
  rewrite<- ih,
  dsimp[fastrev],
  rewrite snoc_append,
  

  rewrite revaux_lemma,
  -/
end


--- Do not add/change anything below this line ---
end ex07