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

--local notation (name := band) x && y := band x y 
--local notation (name := bor) x || y := bor x y

/- 
-- If the above gives an error use the following instead:-/
local notation x && y := band x y
local notation x || y := bor x y


-- First De Morgan law on booleans

-- corresponding law on Prop is:
-- for P, Q : Prop, ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
theorem dm1_b : ∀ x y : bool, ! (x || y) = ! x && ! y :=
begin
  assume x y,
  cases x,
  cases y,
  dsimp [bnot,band,bor],
  refl,
  dsimp [bnot,band,bor],
  refl,
  cases y,
  dsimp [bnot,band,bor],
  refl,
  dsimp [bnot,band,bor],
  refl,
end

-- Excluded middle for booleans

theorem em_bool : ∀ b : bool, (b || ! b) = tt :=
begin
  assume b,
  cases b,
  dsimp [bnot,bor],
  refl,
  dsimp [bnot,bor],
  refl,
end 

------------------------------------------------------------
-- PART II: Alternative definition for `band`

def band2 : bool → bool → bool
| b tt := b
| b ff := ff

reserve infixr ` &&& `:65

--local notation (name := band2) x &&& y := band2 x y 

-- If the above gives an error use the following instead:
local notation x &&& y := band2 x y

-- Using band/&&
theorem band_tt : ∀ x : bool, tt && x = x :=
begin
  assume x,
  dsimp [band],
  refl,
end  

-- Using band2/&&&
theorem band2_tt : ∀ x : bool, tt &&& x = x :=
begin
  assume x,
  cases x,
  dsimp [band2],
  refl,
  dsimp [band2],
  refl,
end  

------------------------------------------------------------
-- PART III: Misc exercises - prove these statements or
-- their negation

def E01 := ∃ b : bool, ∀ x : bool, (b || x) = tt

theorem pf01 : E01 :=
begin
  dsimp [E01],
  existsi tt,
  assume x,
  cases x,
  refl,
  refl,
end 

def E02 := ∀ x : bool, ∃ y : bool, (x || y) = ff

theorem pf02 : ¬ E02 :=
begin
  dsimp [E02],
  assume h,
  have contra : ∃ y: bool, tt || y = ff,
  apply h,
  cases contra with b h2,
  dsimp [bor] at h2,

  contradiction,
end 

def E03 := ∃ b : bool, b && b = ! b

theorem pf03 : ¬ E03 :=
begin
  dsimp [E03],
  assume h,
  cases h with b h2,
  cases b,
  contradiction,
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
  dsimp[band,is_tt],
  assume f,
  contradiction,
  dsimp[band,is_tt],
  assume h,
  constructor,
  constructor,
  exact h,

  cases x,
  dsimp[band,is_tt],
  assume h2,
  cases h2 with l r,
  contradiction,

  dsimp[band,is_tt],
  assume h3,
  cases h3 with l r,
  exact r,
end  

-- `allb f` means `∀ (b : Bool), (f b)`
def allb (f : bool → bool) : bool := (f ff) && (f tt)

theorem allb_ok : 
  ∀ f : bool → bool, 
  is_tt (allb f) ↔ ∀ (x : bool), is_tt (f x) :=
begin
  assume f,
  dsimp [allb],
  have lem: is_tt (f ff && f tt) ↔ is_tt(f ff) ∧ is_tt(f tt),
  apply and_thm,
  cases lem with l r,
  constructor,
  assume h x,
  have g : is_tt (f ff) ∧ is_tt (f tt),
  apply l,
  exact h,
  cases g with gl gr,
  cases x,
  assumption,
  assumption,

  assume x,
  apply r,
  apply l,
  rewrite and_thm,
  constructor,
  apply x,
  apply x,
end

end booleans
