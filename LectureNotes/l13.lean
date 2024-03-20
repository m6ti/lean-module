-- Lecture 13

-- Go through the bs at the start of the lecture




namespace l13

set_option pp.structure_projections false
open nat

--equality on natural numbers is decidable

def eq_nat : ℕ → ℕ → bool
| zero zero := tt
| (succ m) zero := ff
| zero (succ n) := ff
| (succ m) (succ n) := (eq_nat m n)


def Eq_nat (m n : ℕ): Prop
:= m = n

-- complete : if it is true i say yes
lemma eq_nat_compl:  
  ∀ m  : ℕ , --m = n → 
  eq_nat m m = tt:=
begin
  assume m,
  induction m with m' ih,
  reflexivity,
  
  dsimp [ eq_nat],
  rewrite ih,
end

--sound, if i say yes it is true
lemma eq_nat_sound:  
  ∀ m n : ℕ , eq_nat m n = tt → m = n:=
begin
  assume m,
  induction m with m' ih,
  assume n h,
  cases n with n',
  reflexivity,
  dsimp [eq_nat] at h,
  contradiction,

  assume n h,
  cases n with n',

  -- Problem here is we assumed the n too early.
  -- After moving the assumption to a later stage,
  --  we can prove it for ALL n. 
  contradiction,
  dsimp [eq_nat] at h,
  apply congr_arg succ,
  rewrite ih,
  assumption,
end

theorem eq_nat_ok :
  ∀ m n : ℕ , m = n ↔ eq_nat m n = tt:=
begin
  assume m n,
  constructor,
  assume h,
  rewrite h,
  apply eq_nat_compl,
  apply eq_nat_sound,
end

-- eq_nat decided Eq_nat, ie the equality
-- equality on natural numbers is decidable

/-

A predicate PP: A → Prop is decidable
if there is a function p : A → bool such that
∀ a : A, PP a ↔ p a = tt


Prime : ℕ → Prop is decidable
≤ : ℕ → ℕ → Prop is decidable

Halt : Program → Prop
Halt p = program will stop

-/

def Tricky (f: ℕ → bool) : Prop :=
  ∀ n : ℕ, f n = tt

--UNDECIDABLE :( 
 

end l13