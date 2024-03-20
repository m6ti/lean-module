namespace trees2


set_option pp.structure_projections false
variables {A B C : Type}
variable h : A


inductive nat : Type
| zero : nat
| succ : nat → nat
 


inductive Expr : Type
| const : ℕ → Expr
| var : string → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr

open Expr

def exp1 : Expr := plus (const 88) (const 23)

#eval exp1


theorem no_conf : ∀ n : ℕ, ∀ l r : Expr, const n ≠ plus l r :=
 begin
  assume n nh r nn,
  contradiction,
 end

 theorem inj_plus_l : ∀ l r l' r' : Expr , plus l r = plus l' r' → l=l' :=
 begin
   assume a b c d e,
   injection e,
 end

def Env : Type
  := string → ℕ

def my_env : Env
| "x" := 3
| "y" := 5
| _ := 0

#reduce my_env "x"


def evall : Expr → Env → ℕ
| (const n) env := n
| (var v) env := my_env v
| (plus a b) env :=  (evall a env) + (evall b env)
| (times a b) env := (evall a env) * (evall b env)

def e1 : Expr
  := times (var "x") (plus (var "y") (const 2))

def e2 : Expr
  := plus (times (var "x") (var "y")) (const 2)


inductive Instr : Type
| pushC : ℕ → Instr
| pushV : string → Instr
| add : Instr
| mult : Instr

open Instr

def Code : Type
:= list Instr


def Stack : Type
:= list ℕ

def run : Code → Stack → Env → ℕ
| [] [n] env := n
| (pushC n :: c) s env := run c (n:: s) env
| (pushV x :: c) s env := run c (env x :: s) env 
| (add :: c) (m :: n :: s) env := run c ((n + m) :: s) env
| (mult :: c) (m :: n :: s) env := run c ((n * m) :: s) env
| _ _ _ := 0

def c1 : Code
:= [pushV "x",pushV "y",pushC 2,add,mult]

--#eval run c1 [] my_env



 


open nat

def ble : ℕ → ℕ → bool
| 0        n        := tt
| (succ m) 0        := ff
| (succ m) (succ n) := ble m n



inductive Tree : Type
| leaf : Tree
| node : Tree → ℕ → Tree → Tree

open Tree
def ins : ℕ → Tree → Tree
| n leaf := node leaf n leaf 
| n (node l m r) := if ble n m
                    then node (ins n l) m r
                    else node l m (ins n r)

#eval (node leaf) 2 ((node leaf) 6 leaf)


def list2tree : list ℕ → Tree
| [] := leaf
| (n :: ns) := ins n (list2tree ns)

#reduce list2tree [6,2]

def tree2list : Tree → list ℕ
| leaf := []
| (node l m r) := tree2list l ++ m :: tree2list r


#reduce tree2list (list2tree [6,3,8,2,3])

def sort (ns: list ℕ) : list ℕ := tree2list ( list2tree ns) 

#reduce sort [6,3,8,2,3]


inductive AllTree (P : ℕ → Prop) : Tree → Prop
| allLeaf : AllTree leaf
| allNode : ∀ l r : Tree, ∀ m : ℕ,
              AllTree l → P m → AllTree r → AllTree (node l m r)


inductive SortedTree : Tree → Prop
| sortedLeaf : SortedTree leaf
| sortedNode : ∀ l r : Tree, ∀ m : ℕ,
               SortedTree l → AllTree (λ x:ℕ, x ≤ m) l
             → SortedTree r → AllTree (λ x:ℕ, m ≤ x) r
             → SortedTree (node l m r)




inductive Tree2 : Type
| leaf : ℕ → Tree2
| node : Tree2 → Tree2 → Tree2
open Tree2

#eval node (node (leaf 2) (leaf 5))  (leaf 2)



def tree2list : Tree → ℕ 


end trees2



¬ (leave answers blank → negative marking)