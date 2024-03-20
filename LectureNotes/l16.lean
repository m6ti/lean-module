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

def id : A → A
| a := a

def comp : (B → C) → (A → B) → A → C
| g f a := g ( f a)


local notation f ∘ g := comp f g 



-- map (g ∘ f) = (map f) ∘ (map g)

--funext ∀f g : A→ B , (∀ x: A, f x = g x) → f = g

theorem nat_rev: ∀ f : A → B, ∀l : list A,
  map_list f (rev l) = rev (map_list f l) :=
begin
  sorry,
end

open nat
def leb: ℕ→ ℕ→ bool
| 0 n := tt
| (succ m) 0 := ff
| (succ m) (succ n)  := leb m n  

lemma Le2ble : ∀m n : ℕ, m ≤ n → leb m n = tt := sorry,
lemma ble2Le : ∀m n : ℕ, leb m n = tt  → m ≤ n:= sorry,

/-

sort : list ℕ → list ℕ 

sort [6,3,8,2,3] = [2,3,4,6,8]

-/
def ite : bool → A → A → A
| tt a b := a
| ff a b := b

local notation if x then a else b := ite x a b

def insert : ℕ → list ℕ → list ℕ
| n [] := [n]
| n (m :: ns) := if (leb n m) then n :: m :: ns
                            else m :: (insert n ns)

#eval insert 6 [2,3,3,8]

def sort : list ℕ → list ℕ 
| [] := []
| (n :: ns) := insert n (sort ns)

-- #eval sort [6,3,8,2,3]

-- How to prove that sort sorts?
-- What do we mean by sorting?!?!?!?!

/-

  Le_list : ℕ → list ℕ → Prop
  Sorted : list ℕ → Prop

-/

inductive Le_list : ℕ → list ℕ → Prop
| le_nil : ∀ n : ℕ , Le_list n []
| le_cons : ∀m n : ℕ , ∀ ms : list ℕ,
  n ≤ m → Le_list n ms → Le_list n (m::ms)


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
  apply sorted_cons,
  apply ih,
  cases h with _ _ h_le h_s,
  assumption,
  
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





end l15