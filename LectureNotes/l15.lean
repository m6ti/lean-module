namespace l15




set_option pp.structure_projections false
variables {A B C : Type}

 -- [0] ++ [1] ≠ [1] ++ [0]
 -- Watch out for negation of forall. all we need is one example that works.


-- Unit : Type
-- Star : unit
-- list unit = ℕ

theorem comm :  ¬ (∀ A: Type, 
      ∀ as bs : list A,
      as ++ bs = bs ++ as) :=
begin
  assume h,
  have hh: [0] ++ [1] = [1] ++ [0],
  apply h,
  have hhh : 0 = 1,
  dsimp [(++)] at hh,
  injection hh,
  contradiction,
end

-- rev : list A → list A
-- rev [1,2,3] = [3,2,1]
-- rev [1,2,3] = rev (1 :: [2,3])
-- = snoc (rev[2,3]) 1
-- = snoc [3,2] 1
-- = [3,2,1]

-- snoc as b = as ++ b

def snoc : list A → A → list A
| [] a := [a]
| (a :: as) b := a :: (snoc as b)

#eval snoc [3,2] 1

def rev : list A → list A
| [] := []
| (a :: as) := snoc (rev as) a

#eval rev (rev [1,2,3])

-- snoc [1,2] 3 = [1,2,3]
-- rev [1,2,3] = 3 :: rev [1,2]

lemma revsnoc : ∀ as: list A, ∀ a : A, 
    rev (snoc as a) = a :: (rev as) :=
begin
  assume as a,
  induction as with b as' ih,
  dsimp [snoc,rev],
  reflexivity,
  dsimp [snoc,rev],
  rewrite ih,
  reflexivity,
end

theorem revrev : ∀ as : list A, rev ( rev as) = as :=
begin
  assume as,
  induction as with a as' ih,
  dsimp [rev],
  refl,

  dsimp [rev],
  rewrite revsnoc,
  rewrite ih,  
end


/-

 list is a functor
 list : Type → Type
 rev is natrual

-/

def map_list :  (A → B) → list A → list B
| f [] := []
| f (a :: as) := (f a) :: (map_list f as)

/-

identity function!
id : A → A
comp : (B → C) → (A → B) → A → C

-- There are some laws for this ^^

id ∘ f = f
f ∘ id = f

(f ∘ g) ∘ h = f ∘ (g ∘ h)

is this a monoid? Why not
it is a category?

-/


def id : A → A
| a := a

def comp : (B → C) → (A → B) → A → C
| g f a := g ( f a)


local notation f ∘ g := comp f g 

/-

map_list id = id
map_list (g ∘ f) = map_list g ∘ map_list f

-/

lemma map_id_lemma : ∀ as : list A,
  map_list id as = as :=
begin
  assume as,
  induction as with a as' ih,
  refl,
  dsimp [map_list],
  rewrite ih,
  dsimp [id],
  reflexivity,
end

-- f g : A → B
-- ∀ a : A, f a = g a → f = g 

--funext

theorem map_id : map_list (@id A) = id:=
begin
  apply funext,
  apply map_id_lemma,
end

-- 





end l15