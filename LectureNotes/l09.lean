/-  

bool = {tt, ff

  inductive bool : Type
  | tt: bool
  | ff: bool

-/

-- Two = { zero, one }
inductive Two : Type
| zero : Two
| one : Two

-- One = { zero }
inductive One : Type
| zero : One

-- Zero = { }
inductive Zero : Type



namespace bool



-- our first theorem :D
example : ∀ x : bool, x = tt ∨ x = ff :=
begin
  assume george,
  cases george,
  right,
  reflexivity,
  left,
  reflexivity,
end

example : tt ≠ ff :=
begin
  assume h,
  cases h,
end

def bnot : bool → bool
| ff := tt
| tt := ff 

prefix `!`:90 := bnot


example : ∀ x : bool, !(! x) = x :=
begin
  assume x,
  cases x,
  dsimp [bnot],
  -- !(! ff) = ! tt = ff
  reflexivity,
  dsimp [bnot],
  reflexivity,
  -- Reflexivity actually automatically executes dsimp.
  -- However sometimes dsimp needs to be explicitly used.
end

def is_tt : bool -> Prop
| ff := false
| tt := true



-- ⋆ Proving tt ≠ ff 

        example : tt ≠ ff :=
        -- This actually means (tt = ff) -> false
        begin
          assume h,
          cases h,
        end

        example : tt ≠ ff :=
        -- This actually means (tt = ff) -> false
        begin
          assume h,
          contradiction, --YOU CAN USE THIS TOO...
        end

        example : tt ≠ ff :=
        -- This actually means (tt = ff) -> false
        begin
          assume h,
          change is_tt ff,
          -- is_tt ff = false!!
          rewrite<- h,    --USE ASSUMPTION TO REWRITE!!!
          dsimp [is_tt],
          constructor,   -- PROVE TRUE WITH CONSTRUCTOR.
        end



-- A definition of the 'and' function on two bool's.
def band : bool → bool → bool
| tt x := x
| ff x := ff

-- Defining locally that x && y means band x y.
local notation x && y := band x y

-- Proof that band is commutative.
theorem comm_band : ∀ x y : bool, x && y = y && x :=
begin
  assume x y,
  cases x,
  cases y,
  reflexivity,
  reflexivity,
  cases y,
  reflexivity,
  reflexivity,
end

-- Another proof with loads of dsimp[band]'s for some (unknown) reason.
theorem comm_band2 : ∀ x y : bool, x && y = y && x :=
begin
  assume x y,
  cases x,
  dsimp [band],
  cases y,
  dsimp [band],
  reflexivity,
  dsimp [band],
  reflexivity,
  cases y,
  dsimp [band],
  reflexivity,
  dsimp [band],
  reflexivity,
end

def bor : bool → bool → bool
| ff ff := false
| x y := true

def bor2 : bool → bool → bool
| ff x := x
| tt x := tt

local notation x || y := bor x y

--

example : ∀ x y : bool, !(x && y) = (!x) || (!y) :=
begin
  assume x y,
  cases y,
  dsimp[band,bnot,bor],
  reflexivity,

end



end bool
