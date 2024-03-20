variables P Q R: Prop

#check bool -- {tt,ff}
#check ℕ -- {0,1,2,...}
#check list ℕ 
#check ℕ → bool

-- Collectiosn of variables are trees.
variables A B C : Type

--Predicates and relations
/-
Even : ℕ → Prop
Even 2
Even 3

Prime : ℕ → Prop
-- relations: n-ary predicates

≤ : ℕ → ℕ → Prop 

Holds : Tm -> Prop
Holds : Program → Prop

another relation

occurs : A → list A → Prop
occurs 1 [1,2,3] is true
occurs 7 [1,2,3] is false

= : A → A → Prop
-- equality is very important relation. Part of predicate logic. Other relations like even yadidiadia are specific to a particular types
Equality defined for eveery type. !!
-/

variables PP QQ : A →Prop
variable RR : A → B → Prop


  -- Quantifiers: ∀ , ∃ 
  -- assume A = Students, PP x = x is clever.

  #check ∀ x : A , PP x

  #check ∃ x : A, PP x

  #check ∀ x : A , PP x ∧ Q

  -- Scope of a quantifier is as big as possible

#check (∀ x: A, PP x) ∧ Q
-- Here you need brackets for the tree.
-- shadowing
-- if you declare a var again, it shadows the original. 
-- if possible, avoid!!!

example : (∀ x : A, PP x) →
  (∀ x : A, PP x →QQ x )
  → ∀ x : A, QQ x :=
  begin
    assume pp ppqq,
    assume george,
    apply ppqq,
    apply pp,
  end

/-
To prove for all x A pp x
we say assume a
then we add an assumption a : A
and it remains to show PP a.#check

if we know h : ∀ x: A, PP x → QQ x
and we have to prove QQ a 
we say appply h
and it remains to show PP a

if we know h : ∀ x : A, PP x
and we want to show PP a
we say apply h
and we are done.

-/

example : (∀ x: A , PP x ∧ QQ x) ↔ 
  ((∀ x: A, PP x) ∧ (∀ x : A, QQ x)):=
  begin
    constructor,
    assume h,
    

  end