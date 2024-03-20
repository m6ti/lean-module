/-

1a

How are the propositional connectives ↔ 
(if and only if) and ¬ (negation) defined in Lean?


- if and only if  is defined as    A ↔ B = ( A → B ) ∧ ( B → A )
- negation        is defined as        ¬ A = A → ¬

-/



/-

1b

What are the deMorgan laws? 
Which part is not provable in intiutionistic logic?

- DeMorgan laws are the laws that prove
- ¬(P ∧ Q) = ¬P ∨ ¬Q
- and
- ¬(P ∨ Q) = ¬P ∧ ¬Q 


- You can prove the second one of these intuinistically, 
- however the first one you need classical logic.




-/

variables P Q : Prop

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q  :=
begin
  constructor,
  assume h1,
  constructor,
  assume p,
  apply h1,
  left,
  assumption,
  assume q,
  apply h1,
  right,
  assumption,
  assume h2,
  assume h3,
  cases h2 with l r,
  cases h3,
  apply l,
  assumption,
  apply r,
  assumption,
end



/-
c

Which of the following are propositional tautologies in Lean? (without using classical logic) ?
(i) P → (Q ∧ R) ↔ (P → Q) ∧ (P → R)
YES
(ii) (P ∧ Q) → R ↔ (P → R) ∧ (Q → R)
NO
(iii) P → (Q ∨ R) ↔ (P → Q) ∨ (P → R)
NO
(iv) (P ∨ Q) → R) ↔ (P → R) ∨ (Q → R)
YES
(v) (P ∨ Q) → R) ↔ (P → R) ∧ (Q → R)
YES... As false implies anything...

-/
variables R S : Prop

example : P → (Q ∨ R) ↔ (P → Q) ∨ (P → R) :=
begin
  constructor,
  assume h1,
  constructor,
  assume p,
  sorry,
  sorry,
end

example : ¬¬¬P → ¬P :=
begin
  assume nnnp,
  assume p,
  apply nnnp,
  assume np,
  apply np,
  exact p,
end


/-

2a 

reflexivity


2b

variable People : Type
variable Loves : People → People → Prop

Translate the following English expressions into predicate logic using Lean syntax:
(i) Everybody loves somebody.
∀ x:People,∃y:People, Loves x y

(ii) Somebody is loved by everybody.
- WATCH OUT FOR THESE ONES!!
∃ x:People, ∀ y:People, Loves y x

(iii) Love isn’t transitive. (BETWEEN 3 TYPES)
- REVISE DEFINITIONS OF THIS!!
¬ (∀ x y z: People, Loves x y → Loves y z → Loves x z)

(iv) There are people who don’t love anybody.
∃ x : People, ∀ y: People, ¬ Loves x y

(v) Love isn’t symmetric.
¬ (∀ x y: People, Loves x y → Loves y z)




c

How do you specify that A : Type is non-empty?
How do you specify that it is empty?

∃ x: A, true


-/


/-


3a


implb : bool → bool → bool

∀ x y : bool, (x = tt) → (y=tt) ↔ implb x y = tt

def implb : bool → bool → bool
| ff _ : tt
| tt y: y


(you don’t have to prove it).



3b

true
false
true
false



3c

foo 4 = 5

foo 5 = 4

i true
ii true
iii false
-/



/- 

q4

a

inductive list (A: Type) : Type
| nil : List
| cons : A → List → List

b

definition append : list A → list A → list A
| [] l := l
| (h :: s) t := h :: (append s t)

local notation l1 ++ l2 := append l1 l2

Which of the following propositions about ++ hold?
(i) ∀ l : list A, [] ++ l = l
yes
(ii) ∀ l m : list A, l++m = m++l
no
(iii) ∃ l : list A, l++l = l
yes
(iv) ∀ l m1 m2 : list A, l ++ m1 = l ++ m2 → m1 = m2
yes

-/


/-
c

We define trees whose leaves are labelled with natural numbers:
inductive Tree : Type
| leaf : N → Tree
| node : Tree → Tree → Tree

An example is
def t1 : Tree := node (node (leaf 1) (leaf 2)) (leaf 3)

Define a function tree2list : Tree → list N which collects all the leaves in a list.
E.g. tree2list t1 = [1,2,3].

- GO OVER DEFINITIONS

def tree2list : Tree → List ℕ
| leaf n : n
| node l r : (tree2list l) ++ (tree2list r)



d. Given the following definition of permutation of lists in Lean:
inductive Insert : A → list A → list A → Prop
| ins_hd : ∀ a:A, ∀ as : list A,Insert a as (a :: as)
| ins_tl : ∀ a b:A, ∀ as as': list A, Insert a as as'
→ Insert a (b :: as) (b :: as')

inductive Perm : list A → list A → Prop
| perm_nil : Perm [] []
| perm_cons : ∀ a : A, ∀ as bs bs' : list A,
  Perm as bs → Insert a bs bs' → Perm (a :: as) bs'

How do you prove Perm [1,2] [2,1]?

apply perm_cons 1 [2] [2]               : Insert 1 [2] [2,1]
apply perm_cons _ [] []                 : Insert 2 
apply perm_nil,


-/


inductive Expr: Type
| var : string → bool → Expr
| and : Expr → Expr→ Expr
| or : Expr → Expr→ Expr



open Expr

-- Define a type for the environment.
def Envi : Type := string → bool

-- Define the eval function.
def eval : Expr → Envi → bool
| (var negated name) env := 
    let value := env name in
    if negated then not value else value
| (and e1 e2) env := (eval e1 env) && (eval e2 env)
| (or e1 e2) env := (eval e1 env) || (eval e2 env)


def neg :Expr → Expr
| var b x := var !b x
| and e1 e2 := or (neg e1) (neg e2)
| or e1 e2 := and (neg e1) (neg e2)
