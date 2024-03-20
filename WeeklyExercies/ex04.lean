/-
COMP2065-IFR Exercise 04
(Booleans) 

    This exercise has 2 parts.

    The first part is "logic chess" which has slightly different rules
    than logic poker but see below. The 2nd part asks you to prove that
    orb on booleans corresponds to the logical or and define an operation
    to compute existential quantification on booleans and prove it correct. 

    Don't worry, if you can't do the existential quantification part. 
    This is intended as a challenge and only counts for 20% of the 
    exercise. 
-/

namespace ex04
def bnot : bool → bool 
| tt := ff
| ff := tt 

def band : bool → bool → bool 
| tt b := b
| ff b := ff

def bor : bool → bool → bool 
| tt b := tt
| ff b := b

def is_tt : bool → Prop 
| tt := true
| ff := false

/- --- Do not add/change anything above this line --- -/


local notation x && y := band x y 
local notation x || y := bor x y
/-
If you get an error update your lean or use:
local notation x && y := band x y 
local notation x || y := bor x y
-/


prefix `!`:90 := bnot

/-
PART I (60%)
============
Logic chess

Unlike logic poker in logic chess there is no guessing. You either
prove the proposition or you prove its negation.

Consider the following examples:
-/
def Ch0 := ∀ x : bool, x=x
def Ch00 := ∀ x : bool, x ≠ x

/- the first one is provable, hence we prove it -/

theorem ch0 : Ch0 :=
begin
  assume x,
  reflexivity
end

/- the second one is false, hence we prove its negation -/

theorem ch00 : ¬ Ch00 :=
begin
  assume h,
  have g : tt ≠ tt,
  apply h,
  apply g,
  reflexivity,
end


def Ch01 := ∀ x : bool, ! x = x
def Ch02 := ∀ x:bool,∃ y:bool, x = y
def Ch03 := ∃ x:bool,∀ y:bool, x = y
def Ch04 := ∀ x y : bool, x = y → ! x = ! y
def Ch05 := ∀ x y : bool, !x = !y → x = y
def Ch06 := ∀ x y z : bool, x=y ∨ y=z 
def Ch07 := ∃ b : bool, ∀ y:bool, b || y = y 
def Ch08 := ∃ b : bool, ∀ y:bool, b || y = b
def Ch09 := ∀ x : bool, (∀ y : bool, x && y = y) ↔ x = tt 
def Ch10 := ∀ x y : bool, x && y = y ↔ x = ff

/-
Name your theorems ch01, ch02, ..., ch10. chXX should either
be a proof of ChXX or a proof of ¬ ChXX, so either delete the
? or replace it by a ¬.
-/

-- theorem ch01 : ? Ch01 :=

theorem ch01 : ¬ Ch01 :=
begin
  assume h,
  have g : !ff = ff,
  apply h,
  cases g,
end

-- theorem ch02 : ? Ch02 :=

theorem ch02 : Ch02 :=
begin
  assume a,
  existsi a,
  reflexivity,
end

-- theorem ch03 : ? Ch03 :=
theorem ch03 : ¬ Ch03 :=
begin
  dsimp [Ch03],
  assume h,
  cases h with h1 h2,
  cases h1,
  have contra: (ff = tt),
  apply h2,
  contradiction,
  have contra: (tt = ff),
  apply h2,
  contradiction,
end

-- theorem ch04 : ? Ch04 :=
theorem ch04 : Ch04 :=
begin
  assume x y,
  assume xy,
  cases xy,
  reflexivity,
end
-- theorem ch05 : ? Ch05 :=
theorem ch05 : Ch05 :=
begin
  dsimp[Ch05],
  assume x y,
  cases x,
  cases y,
  assume nxny,
  reflexivity,
  assume nottrue,
  dsimp [bnot] at nottrue,
  contradiction,
  cases y,
  assume nottrue,
  dsimp [bnot] at nottrue,
  contradiction,
  assume tt,
  reflexivity,
end

-- theorem ch06 : ? Ch06 :=
theorem ch06 : ¬ Ch06 :=
begin
  dsimp[Ch06],
  assume h,
  have h:(tt=ff ∨ ff=tt),
  apply h,
  cases h with l r,
  contradiction,
  contradiction,
end

-- theorem ch07 : ? Ch07 :=
theorem ch07 : Ch07 :=
begin 
  dsimp[Ch07],
  existsi ff,
  assume y,
  dsimp[bor],
  reflexivity,
  -- This is because we use pattern matching to match the bor pattern :)
end
-- theorem ch08 : ? Ch08 :=

theorem ch08 : Ch08 :=
begin 
  dsimp[Ch08],
  existsi tt,
  assume y,
  dsimp[bor],
  reflexivity,
end

-- theorem ch09 : ? Ch09 :=
theorem ch09 : Ch09 :=
begin 
  dsimp[Ch09],
  assume x,
  constructor,
  assume h1,
  cases x,
  dsimp[band] at h1,
  apply h1,
  reflexivity,
  assume xt y,
  cases x,
  contradiction,
  dsimp[band],
  reflexivity,
end

-- theorem ch10 : ? Ch10 :=
theorem ch010 :¬ Ch10 :=
begin 
  dsimp[Ch10],
  assume not,
  have contra : ( ff && tt = tt ↔ ff = ff),
  apply not,
  dsimp [band] at contra,
  cases contra with h1 h2,
  have contra : ( ff = tt),
  apply h2,
  reflexivity,
  contradiction,
end

/- 
PART II (40%)
=============

a) Show the correctness of or:
-/
theorem orb_ok : ∀ x y : bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  assume x y,
  constructor,
  cases x,
  dsimp [bor,is_tt],
  assume h1,
  cases h1,
  contradiction,
  assumption,
  dsimp [bor, is_tt],
  assume h2,
  constructor,
  cases x,
  assume h3,
  dsimp [bor] at h3,
  right,
  assumption,
  assume h4,
  dsimp [bor] at h4,
  left,
  assumption,
end

/-
b) Define an operation 
-/

def exb  (f : bool → bool) : bool
    := (f ff) || (f tt) -- (f tt = tt) || (f ff = tt)

-- exB F
/-

here you can use boolean operations 
which have been defined already.

Prove that it computes existential quantification:
-/
theorem exb_ok : ∀ f : bool → bool, is_tt (exb f) ↔ ∃ x : bool, is_tt (f x) :=
begin
  assume f,
  dsimp [exb],
  have lem :  (is_tt (f ff)) ∨ (is_tt (f tt)) ↔ (is_tt (f ff || f tt)) ,
  apply orb_ok,
  cases lem with l r,
  constructor,
  assume h1,
  have g:is_tt (f ff) ∨ is_tt (f tt),
  apply r,
  exact h1,
  cases g,
  existsi ff,
  exact g,
  existsi tt,
  exact g,


  assume h2,
  apply l,
  cases h2 with x h3,
  cases x,
  left,
  exact h3,
  right,
  exact h3,
end
/-
(*) the exb part is difficult, you only loose 20% if you don't do it.
-/


/- --- Do not add/change anything below this line --- -/
end ex04
