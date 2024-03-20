namespace l15




set_option pp.structure_projections false
variables {A B C : Type}


def snoc : list A → A → list A
| [] a := [a]
| (a :: as) b := a :: (snoc as b)

#eval snoc [3,2] 1

def rev : list A → list A
| [] := []
| (a :: as) := snoc (rev as) a

#eval rev (rev [1,2,3])

def map_list :  (A → B) → list A → list B
| f [] := []
| f (a :: as) := (f a) :: (map_list f as)


def ite : bool → A → A → A
| tt a b := a
| ff a b := b
local notation if x then a else b := ite x a b

open nat
def leb: ℕ→ ℕ→ bool
| 0 n := tt
| (succ m) 0 := ff
| (succ m) (succ n)  := leb m n  

def insert : ℕ → list ℕ → list ℕ
| n [] := [n]
| n (m :: ns) := if (leb n m) then n :: m :: ns
                            else m :: (insert n ns)

#eval insert 6 [2,3,3,8]

def sort : list ℕ → list ℕ 
| [] := []
| (n :: ns) := insert n (sort ns)

#eval sort [6,2,3,3,8]


lemma Le2ble : ∀m n : ℕ, m ≤ n → leb m n = tt := sorry,
lemma ble2Le : ∀m n : ℕ, leb m n = tt  → m ≤ n:= sorry,



-- if n is leb m for every one in list, then return the following
inductive Le_list : ℕ → list ℕ → Prop
| le_nil : ∀ n : ℕ , Le_list n []
| le_cons : ∀m n : ℕ , ∀ ms : list ℕ,
  n ≤ m → Le_list n (m::ms)

/-
  We dont need to know this! 

| le_cons : ∀m n : ℕ , ∀ ms : list ℕ,
  n ≤ m → Le_list n ms → Le_list n (m::ms)

  Prove that the two versions of Le_list are equivalent
  (If the list is sorted)

-/

-- We make sure n fits in the start of the list.
inductive Sorted : list ℕ→ Prop
| sorted_nil : Sorted []
| sorted_cons : ∀ n : ℕ, ∀ns : list ℕ,
    Sorted ns → Le_list n ns → Sorted (n::ns)          

open Le_list Sorted

lemma sgl_sorted : ∀n:ℕ, Sorted [n] :=
begin
  assume n,
  apply sorted_cons,
  apply sorted_nil,
  apply le_nil,
end  

lemma le_insert_lem : ∀n' n: ℕ, ∀ns: list ℕ,
Le_list n' ns → n' ≤ n → Le_list n' (insert n ns)
:=
begin
  sorry,
end

lemma leb_lem : ∀ n n': ℕ, leb n n' = ff → n' ≤ n:=
begin
  assume n n' h,
  apply ble2Le,
  sorry,
end  

lemma insert_lem : ∀ ns : list ℕ, ∀ n: ℕ,
    Sorted ns → Sorted (insert n ns) :=
begin
  assume ns n h,
  induction ns with n' ns' ih,
  dsimp[ insert ],
  apply sgl_sorted,

  cases hh: ( leb n n' ),
  dsimp [insert],
  rewrite hh,
  dsimp[ite],
  
  cases h with _ _ h_le h_s,

  apply sorted_cons,
  apply ih,
  assumption,

  -- leb n n' = ff → n' ≤ n
  -- Le_list n' ns → n' ≤ n → Le_list n' (insert n ns')

  apply le_insert_lem,
  assumption,
  apply leb_lem,
  assumption,

  -- it could be true.
  

end


theorem sort_sorts : ∀ ns : list ℕ,
  Sorted (sort ns) := 
begin 
  assume ns,
  induction ns with n' ns' ih,
  dsimp [sort],

  apply sorted_nil,
  dsimp [sort],
  apply insert_lem,
  assumption,
end  


-- Permutation
-- Perm : list A → list A → Prop
-- Perm l l' = l and l' can be obtained by changing the order of the elements.

-- Perm [1,2,3,3] [3,1,2,3]
-- ¬ Perm [1,2,3] [3,1]
-- ¬ Perm [1,2,3,3] [1,2,3]


--Insert 1 [2,3] [2,1,3]
inductive Insert : A → list A → list A → Prop
| insert_hd  : ∀ a: A, ∀ as :list A, Insert a as (a :: as)
| insert_tl : ∀ a b : A, ∀ bs abs :list A, 
                      Insert a bs abs 
                      → Insert a (b::bs) (b::abs)



inductive Perm : list A → list A → Prop
| perm_nil : Perm [] []
| perm_cons : ∀a b: A, ∀ as bs bs': list A, Perm as bs → Insert a bs bs' 
      → Perm (a:: as) bs'

open Insert Perm

theorem refl_perm : ∀as : list A, Perm as as :=
begin
  assume as,
  induction as with a as' ih,
  apply perm_nil,
  apply perm_cons,
  assumption,
  exact ih,

  apply insert_hd,
end

lemma insert_insert : ∀ n: ℕ, ∀ ns: list ℕ, Insert n ns (insert n ns) :=
begin
  assume n ns,
  induction ns with n' ns' ih,
  dsimp [insert],
  apply insert_hd,

  dsimp [insert],
  cases (leb n n'),
  dsimp [ite],
  apply insert_tl,
  assumption,

  dsimp [ite],
  apply insert_hd,
end

theorem perm_sort: ∀ l:list ℕ, Perm l (sort l):=
begin
  assume l,
  induction l with a l' ih,
  dsimp [sort],
  apply perm_nil,
  dsimp [sort],
  apply perm_cons,
  assumption,
  exact ih,
  apply insert_insert,
end




end l15