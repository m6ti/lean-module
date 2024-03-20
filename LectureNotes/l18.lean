-- Lecture 18 : expression trees & compiler


namespace l18

set_option pp.structure_projections false

inductive Expr : Type
| const : ℕ → Expr
| var : string → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr

open Expr
-- x * (y + 2)
def e1 : Expr
  := times (var "x") (plus (var "y") (const 2))

-- (x * y) + 2
def e2 : Expr
  := plus (const 2) (times (var "y") (var "x"))

-- #eval e1
def Env : Type
  := string → ℕ

-- undefined = 0 

def eval : Expr → Env → ℕ 
| (const n) env := n
| (var x) env := env x
| (plus e1 e2) env := (eval e1 env)+(eval e2 env)
| (times e1 e2) env := (eval e1 env)*(eval e2 env)

def env0 : Env
| "x" := 3
| "y" := 5
| _ := 0

--#eval (eval e1 env0)
--#eval (eval e2 env0)

inductive Instr : Type
| pushC : ℕ → Instr
| pushV : string → Instr
| add : Instr 
| mult : Instr

open Instr

@[reducible]
def Code : Type
:= list Instr


def Stack : Type
:= list ℕ

def run : Code → Stack → Env → ℕ
| [] [n] env := n
| (pushC n :: c) s env 
  := run c (n::s) env
| (pushV x::c) s env :=
  run c (env x :: s) env
| (add :: c) (m :: n :: s) env := 
  run c ((n + m) :: s) env
| (mult :: c) (m :: n :: s) env := 
  run c ((n * m) :: s) env


def c1 : Code
:= [pushV "x", pushV "y", pu]




end l18