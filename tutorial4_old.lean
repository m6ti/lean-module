def bor_duplicate : bool → bool → bool
| ff ff := false
| x y := true



prefix `!`:90 := bnot



def E02:= ∀ x:bool, (∃ y: bool, (x || y) = ff)



theorem pf02 : ¬E02:=
begin
  dsimp[E02],
  assume all,
  have contra : ∃ y:bool, tt || y = ff,
  apply all tt,
  cases contra with b pfb,
  dsimp [bor] at pfb,
  contradiction,
end


def E03 := ∃ b: bool , b && b = ! b

theorem pf03 : ¬E03:=
begin
  dsimp[E03],
  assume ex,
  cases ex with b eqb,
  cases b,
  dsimp [band,bnot] at eqb,
  contradiction,
  dsimp [band,bnot] at eqb,
  contradiction,
end 


def is_tt : bool → Prop
| ff := false
| tt := true

--one is a boolean, the other is a proposition.



-- 'and' does case analysis on the first one, in this case x
theorem and_thm :
  ∀ x y: bool, (x && y) ↔ (is_tt x) ∧ (is_tt y):=
begin
  assume x y,
  constructor,
  cases x,
  dsimp[band,is_tt],
  assume f,
  cases f,
  dsimp[band, is_tt],
  assume tty,
  constructor,
  constructor,
  assumption,
  exact tty,
  
  cases x,
  dsimp[band,is_tt],
  assume conj,
  cases conj with f tty,
  cases f,
  dsimp[band, is_tt],
  assume conj,
  cases conj with t tty,
  exact tty,

end


-- `allb f` means `∀ (b:bool), (f b)` 
def allb (f:bool -> bool) : bool := 
  (f ff) && (f tt)


theorem allb_ok :
  ∀ f: bool → bool,
  is_tt (allb f) ↔ ∀ (x:bool) , is_tt (f x) :=
begin
  assume f,
  dsimp[allb],
  have lem : (is_tt (f ff && f tt)) ↔ (is_tt (f ff)) ∧ (is_tt (f tt)),
  apply and_thm (f ff) (f tt),
  cases lem with l r,
  constructor,

  

end