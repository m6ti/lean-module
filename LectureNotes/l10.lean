/-
Lecture 10 : Natural Numbers

Peano arithmetic 189x- PA.

-/

namespace l10
set_option pp.structure_projections false
open nat

/- 
bool = {ff , tt}

inductive bool : Type
| ff : bool
| tt : bool


tt ≠ ff 
∀ x :bool , x=ff ∨ x = tt

P : bool → Prop
P ff → P tt -> ∀ x : bool, P x

-/


/-

ℕ = {0,1,2,3}
  = {zero, succ zero, succ( succ zero ), ...}
inductive ℕ:Type
| 0: ℕ
| 1: ℕ 
...

inductive ℕ : Type
| zero : ℕ
| succ : ℕ → ℕ

∀ n : ℕ , zero ≠ succ n

-/


example : ∀ n : ℕ , zero ≠ succ n :=
begin
  assume n,
  contradiction, -- Works for any constructor types!! e.g. different defintions
end


/-
  Backward function for 
-/
def pred : ℕ → ℕ
|   zero   := zero
| (succ m) := m

#eval (pred 5)


-- This is saying successor is injective. Constructors are always injective, and different consturctors are different.
example : ∀ m n, succ m = succ n → m = n :=
begin
  assume m n,
  assume h,
  change pred (succ m) = n,
  rewrite h,  
  dsimp [pred],
  refl,
end

--Lovely stuff. use change!
-- SHORTCUT

example : ∀ m n, succ m = succ n → m = n :=
begin
  assume m n h,
  injection h,
end
-- inejction knows that the constructors are injective.

-- Lets prove these are ALL the natural numbers

variable P : ℕ → Prop
--INDUCTION!!
-- ∞ = succ ∞ This doesn't contradict this, not reachable by 0 and successor. We can rule this out with induction, but not with the second definition.
example: P zero → (∀ n:ℕ, P n → P (succ n))
  → ∀ i : ℕ , P i :=
begin
  assume p0 ps i,
  induction i with j ih,
  assumption,
  apply ps,
  assumption,
end

--
example: P zero → 
  (∀ n:ℕ, P (succ n))
  → ∀ i : ℕ , P i :=
begin
  assume p0 ps i,
  cases i with j, -- Gives you a case for 0 and case for succ. Similar to induction but less power.
  assumption,
  apply ps,
end


def double : ℕ→ ℕ
| zero := zero
| (succ m) := succ (succ (double m))

-- RECURSION!!! 💀

def add : ℕ → ℕ → ℕ
| n zero := n
| zero n := n
| (succ n) (succ m) := succ( succ (add m n))

--WITHOUT REMAINDER
def half : ℕ → ℕ
| zero := zero
| (succ zero) := zero --ignore remainder ;)
| (succ(succ m)) := succ (half m)



/-
-- half 3 = succ (half 1) = 1
-- half 3 = succ (half 3) = succ (1) = 2

-- half 3 = half (succ (succ 1)) = succ( half 1) = succ  0 = 1
-- half 5 = half (succ (succ 3)) = succ( half 3) = succ (1) = 2
-/
example : ∀ n:ℕ, half (double n) = n:=
begin

  assume n,
  induction n with n' ih,--prove for 0 and succ.
  --dsimp [ double, half ]
  refl,
  dsimp[double],
  dsimp[half],
  rewrite ih,
end

-- UNDERSTAND THIS ONE PROOF. SHOULDNT BE TOO DIFFICULT.

