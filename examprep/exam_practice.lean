/-

1a
    
    P ↔ Q = (P → Q) ∧ (Q → P)
    
    P → ¬
    
-/

/-

1b

  ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q

  ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q

-/


/-

1c

  (true)    P → (Q ∧ R) ↔ (P → Q) ∧ (P → R)
 (false)   (P ∧ Q) → R ↔ (P → R) ∧ (Q → R)
  (false)    P → (Q ∨ R) ↔ (P → Q) ∨ (P → R)
      (ONLY CLASSICALLY!!! → NOT PROVABLE INTUINISTICALLY)

  (true)  ((P ∨ Q) → R) ↔ (P → R) ∨ (Q → R)     
  (true)  ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R)     


-/


/-

1d
-/
variables P : Prop



theorem negate:  ¬¬¬P → ¬P:=
begin
    assume h1,
    assume h2,
    apply h1,
    assume h3,
    apply h3,
    exact h2,
end









theorem negate:  ¬¬¬P → ¬P:=
begin
  assume nnnp,
  assume p,
  apply nnnp,
  assume nnp,
  apply nnp,
  exact p,
end

variables a: Type
theorem equals: a = a:=
begin
  reflexivity,
end

/-

2a

  h : a = b?

  How do you use this assumption?
    
  -  rewrite h
-/


/- 

2b

  Loves x y   MEANS   x loves y

  variable People : Type
  variable Loves : People → People → Prop

  (i) Everybody loves somebody.
  
    ∀ x : People, ∃ y : People, Loves x y

  (ii) Somebody is loved by everybody.

    ∃ x : People, ∀ y : People, Loves x y 

  (iii) Love isn’t transitive.

    ¬ (∀ x y z : People, Loves x y → Loves y z → Loves x z)

  (iv) There are people who don’t love anybody.

    ∃ x : People, ∀ y : People, ¬ Loves x y

  (v) Love isn’t symmetric.

-/

/- 

2c

  How do you specify that A : Type is non-empty? How do you specify that it is empty?

  non empty :  ∃ x: A, true

  empty : ∀ x : A, false

-/

/-

3a
  Define function

  implb : bool → bool → bool

  such that 
  ∀ x y : bool,
 (x = tt) → (y=tt) ↔ implb x y = tt

  def implb : bool → bool → bool
  | tt b := b
  | ff b := tt

-/

/-

3b

  (i) ∀ x : bool, ∃ y:bool, x ≠ y
    
    we can ?!?!?

  (ii) ∃ x : bool, ∀ y:bool, x ≠ y

    we can't

  (iii) ∀ x : bool, ∃ y:bool, x=y

    we can 
  
  (iv) ∃ x : bool, ∀ y:bool, x = y

    we can't

  For anything related to bools, we can either prove the thing,
  or its negation!

-/

open nat

def foo : ℕ → ℕ 
| zero := 1
| (succ zero) := 0
| (succ (succ n)) := succ (succ (foo n))


--#eval foo 5
--#eval foo 4

/-

3c

  def foo : N → N
  | zero := 1
  | (succ zero) := 0
  | (succ (succ n)) := succ (succ (foo n))

  Foo 4?

  Foo 5?

  (i) [true] foo is injective.
        ∀ x y : N, foo x = foo y → x=y
  (ii) [true] foo is surjective.
        ∀ y : N, ∃ x : N , foo x = y
  (iii) [false] foo has a fixpoint.
        ∃ x:N, foo x = x

-/

inductive List (A : Type) : Type
| nil : List
| cons : A → List → List

/- 

4a 

  What is the definition of list as an inductive type in Lean?
   
  inductive List (A : Type) : Type
  | nil : List
  | cons : A → List → List

-/

/-

4b

  (i) ∀ l : list A, [] ++ l = l
      true
  (ii) ∀ l m : list A, l++m = m++l
      false
  (iii) ∃ l : list A, l++l = l
      true
  (iv) ∀ l m1 m2 : list A, l ++ m1 = l ++ m2 → m1 = m2
      true
-/


/-
4c

  def tree2list: Tree → list ℕ
  | leaf n := [n]
  | node l r := (tree2list l) ++ (tree2list r) 

-/


-- 4d
variables {A : Type}


inductive Insert : A → list A → list A → Prop
| ins_hd : ∀ a:A, ∀ as : list A,Insert a as (a :: as)
| ins_tl : ∀ a b:A, ∀ as as': list A, Insert a as as'
  → Insert a (b :: as) (b :: as')

open Insert

inductive Perm : list A → list A → Prop
| perm_nil : Perm [] []
| perm_cons : ∀ a : A, ∀ as bs bs' : list A,
  Perm as bs → Insert a bs bs' → Perm (a :: as) bs'


open Perm

example : Perm [1,2] [2,1] :=
begin
  apply perm_cons 1 [2] [2],
  apply perm_cons 2 [] [],
  apply perm_nil,
  apply ins_hd,
  apply ins_tl,
  apply ins_hd,
end

example : Perm [1,3,2] [2,1,3] :=
begin
  apply perm_cons 1 [3,2] [2,3],
  apply perm_cons 3 [2] [2],
  apply perm_cons _ [] [],
  apply perm_nil,
  apply ins_hd,
  apply ins_tl,
  apply ins_hd,
  apply ins_tl,
  apply ins_hd,
end

/-

  apply perm_cons


-/