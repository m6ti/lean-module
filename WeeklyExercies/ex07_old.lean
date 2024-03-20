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

#eval revaux [1,2,3,4,5] [333]

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

#eval revaux [1,2,3] [444,555]

#eval revaux [1,2,3] [444] ++ [555]

#eval rev [1,2,3] ++ [444,55]

-- ⊢ revaux as' [a', a] = rev (a' :: as') ++ [a]

lemma revauxplus : ∀ as:list A, ∀ a a': A, revaux as [a', a] = revaux as [a']++ [a]:=
begin
  sorry,
end

lemma revauxappbackup : ∀ as bs:list A, ∀ b: A, as ++ [b] = bs ++ [b] ↔ as = bs:=
begin
  sorry,
end

lemma revauxapp : ∀ as:list A,∀ a b:A ,revaux as [a] ++ [b]= rev as ++ [a] ++ [b] → revaux as [a] = rev as ++ [a]:=
begin
  assume as a b h,
  rewrite<- revauxappbackup,
  exact h,
end

lemma revauximp : ∀ as : list A, ∀ a a':A , revaux as [a] = rev as ++ [a] → revaux as [a'] = rev as ++ [a'] :=
begin
  assume as,
  induction as with a as' ih,
  assume a a' h,
  reflexivity,

  assume a' a'' h,
  dsimp [revaux],
  rewrite rev,
  rewrite snoc_append,
  -- prove
  rewrite revauxplus,

  dsimp [revaux] at h,
  rewrite rev at h,
  rewrite snoc_append at h,
  rewrite revauxplus at h,

  apply congr_arg (++ [a'']),
  apply ih,
  -- prove
  apply revauxapp,
  exact h,
end

lemma revauxrev : ∀ as : list A,∀ a: A, revaux as [a] = rev as ++ [a]:=
begin 
  assume as,
  induction as with a' as' ih,
  assume a,
  dsimp [rev, revaux],
  reflexivity,

  assume a,
  dsimp [revaux],
  rewrite rev,
  rewrite snoc_append,
  rewrite revauxplus,
  apply congr_arg (++ [a]),
  apply ih,
/-
  cases as' with a l,
  dsimp [rev,revaux,snoc,(++)],
  reflexivity,
  rewrite revaux,
  -/
end


theorem fastrev_thm : ∀ as : list A , fastrev as = rev as :=
begin
  assume as,
  rewrite fastrev,
  induction as with a as' ih,
  reflexivity,

  dsimp[ rev, revaux ],
  rewrite snoc_append,
  rewrite revauxrev,

end


--- Do not add/change anything below this line ---
end ex07