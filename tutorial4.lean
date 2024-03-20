/-
COMP2065 Tutorial 4
-/

namespace booleans

------------------------------------------------------------
-- PART I: Intro to booleans

/-
inductive bool : Type
| ff : bool
| tt : bool
-/

def bnot : bool → bool
| tt := ff
| ff := tt

def band : bool → bool → bool
| tt b := b
| ff b := ff

def bor : bool → bool → bool
| tt b := tt
| ff b := b

prefix `!`:90 := bnot
reserve infixr ` && `:65
reserve infixr ` || `:60

local notation x && y := band x y 
local notation x || y := bor x y

/- 
-- If the above gives an error use the following instead:
local notation x && y := band x y
local notation x || y := bor x y
-/

-- First De Morgan law on booleans

-- corresponding law on Prop is:
-- for P, Q : Prop, ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
theorem dm1_b : ∀ x y : bool, ! (x || y) = ! x && ! y :=
begin
  assume x y,
  cases x,
  dsimp[band,bor,bnot],
  reflexivity,
  dsimp[band,bor,bnot],
  reflexivity,
end

-- Excluded middle for booleans

theorem em_bool : ∀ b : bool, (b || ! b) = tt :=
begin
  assume b,
  cases b,
  dsimp[bor, band, bnot],
  reflexivity,
  dsimp[bor, band, bnot],
  reflexivity,
end 

------------------------------------------------------------
-- PART II: Alternative definition for `band`

def band2 : bool → bool → bool
| b tt := b
| b ff := ff

reserve infixr ` &&& `:65

local notation x &&& y := band2 x y 

-- If the above gives an error use the following instead:
--local notation x &&& y := band2 x y

-- Using band/&&
theorem band_tt : ∀ x : bool, tt && x = x :=
begin
  assume x,
  dsimp[band],
  reflexivity
end  

-- Using band2/&&&
theorem band2_tt : ∀ x : bool, tt &&& x = x :=
begin
  assume x,
  cases x,
  dsimp[band2],
  reflexivity,
  dsimp[band2],
  reflexivity,
end  

------------------------------------------------------------
-- PART III: Misc exercises - prove these statements or
-- their negation

def E01 := ∃ b : bool, ∀ x : bool, (b || x) = tt

theorem pf01 : E01 :=
begin
  dsimp[E01],
  existsi tt,
  assume x,
  dsimp[bor],
  reflexivity,
end  

def E02 := ∀ x : bool, ∃ y : bool, (x || y) = ff

theorem pf02 : ¬ E02 :=
begin
  dsimp[E02],
  assume all,
  have contra : ∃ y:bool, tt || y = ff,
  apply all tt,
  cases contra with b pfb,
  dsimp [bor] at pfb,
  contradiction,
end 

def E03 := ∃ b : bool, b && b = ! b

theorem pf03 : ¬ E03 :=
begin
  dsimp[E03],
  assume h,
  cases h with l r,
  cases l,
  dsimp [band] at r,
  contradiction,
  dsimp [band] at r,
  contradiction,
end

------------------------------------------------------------
-- PART IV: Relating bool and Prop

/-
|   Prop   |    Bool   |
|----------|-----------|
|   true   |    tt     |
|  false   |    ff     |
|    ¬     | bnot (!)  |
|    ∧     | band (&&) |
|    ∨     | bor  (||) |
|    ↔     |     =     |
-/

-- is_tt lifts booleans to propositions
def is_tt : bool → Prop
| ff := false
| tt := true

theorem and_thm : 
  ∀ x y : bool, 
  is_tt (x && y) ↔ (is_tt x) ∧ (is_tt y) := 
begin
  assume x y,
  constructor,
  cases x,
  dsimp [band,is_tt],
  assume f,
  contradiction,
  dsimp [band,is_tt],
  assume tty,
  constructor,
  constructor,
  assumption,

  cases x,
  dsimp [band,is_tt],
  assume conj,
  cases conj with f tty,
  cases f,
  dsimp [band,is_tt],
  assume conj,
  cases conj with t tty,
  assumption,
end  

-- `allb f` means `∀ (b : Bool), (f b)`
def allb (f : bool → bool) : bool := 
  (f ff) && (f tt)

theorem allb_ok : 
  ∀ f : bool → bool, 
  is_tt (allb f) ↔ ∀ (x : bool), is_tt (f x) :=
begin
  assume f,
  dsimp[allb],
  have lem : (is_tt (f ff && f tt)) ↔ (is_tt (f ff)) ∧ (is_tt (f tt)),
  apply and_thm (f ff) (f tt),
  cases lem with l r,
  constructor,
  assume h x,
  have g:is_tt (f ff) ∧ is_tt (f tt),
  apply l,
  exact h,
  cases g with l r,
  cases x,
  assumption,
  assumption,

  assume h,
  apply r,
  constructor,
  apply h,
  apply h,


end







def implb : bool → bool → bool
| ff b := tt
| tt b := b

example : ∀ x y: bool,(is_tt x → is_tt y) ↔ is_tt(implb x y):=
begin
  assume x y,
  constructor,
  cases x,
  cases y,
  dsimp[implb,is_tt],
  assume h2,
  constructor,
  dsimp[implb,is_tt],
  assume h3,
  constructor,
  cases y,
  dsimp[implb,is_tt],
  assume h4,
  apply h4,
  constructor,
  dsimp[implb,is_tt],
  assume h5,
  constructor,

  assume h1,
  assume h2,
  cases x,
  cases h2,
  cases y,
  cases h1,
  constructor,
end


end booleans



def theorem2 : ∀ (x y z : bool), x = y ∨ y = z -> ∀ (x y z : bool), (x ≠ y) ∧ (y ≠ z):=
begin
  sorry,
end

/-lemma change1 : ∀ x y z:bool, 
    ((x = tt ∨ tt = z )∨ (x = ff ∨ ff = z))
    ↔ (x = y ∨ y = z):=
begin
  assume x y z,
  constructor,
  assume h1,
  cases h1 with h2 h3,
  cases h2 with h4 h5,
  cases y,



end-/

variables A: Prop
variables PP QQ : A → Prop

example : (∃ x : A, PP x ∨ QQ x) ↔ (∃ x : A , PP x) ∨ (∃ x : A, QQ x) :=
begin
  constructor,
  assume h,
  cases h with a ha,
  cases ha with pa qa,
  left,
  existsi a,
  exact pa,
  right,
  existsi a,
  exact qa,
  assume h,
  cases h with hp hq,
  cases hp with a pa,
  existsi a,
  left,
  exact pa,
  cases hq with a qa,
  existsi a,
  right,
  exact qa,
end
