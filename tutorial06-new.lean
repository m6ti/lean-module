/- COMP2065 Autumn 2023
# Tutorial 6: Natural Numbers Redux
  + Decidable predicates and relations
  + Gauss's Kindergarten Theorem
-/

namespace tutorial06

set_option pp.structure_projections false


open nat

def add : ℕ → ℕ → ℕ 
| m zero     := m
| m (succ n) := succ (add m n)

local notation  m + n := add m n

def mul : ℕ → ℕ → ℕ 
| m 0 := 0
| m (succ n) := m + (mul m n)
local notation  m * n := mul m n


theorem add_lneutr : ∀ n : ℕ , 0 + n = n := sorry
theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) := sorry
theorem mul_comm :  ∀ m n : ℕ , m * n = n * m := sorry

lemma succ_add : ∀ m n : ℕ, succ(m + n) = (succ m) + n :=
begin 
  assume m n,
  induction n with n' ih,
  dsimp[(+)],
  refl,
  dsimp[(+)],
  rewrite ih,
end 


/-
## Decidable Predicates and Relations

A predicate P : X → Prop is said to be **decidable** if there is a
boolean-valued function p : X → bool which **decides** P:
- **Soundness**: For every x:X that r "says satisfies P" 
    (p x = tt), it is indeed the case that P x
- **Completeness**: For every x:X that *does* satisfy P (i.e. P x holds), 
    p "detects it", i.e. p x = tt

I.e. the decider function p *computes*/*decides* for each x whether
       P x ↔ true        or       P x ↔ false   
-/
def Allb (f : bool → bool) : Prop :=
  ∀ x : bool, f x = tt 

def f (x : bool) : bool := x 
#check Allb f
-- Doesn't tell us if it is true or false?!!!??! - Because it is a Prop
-- Write decider function allb.

def allb (f : bool → bool) : bool :=
  f tt && f ff

theorem allb_ok : ∀ f : bool → bool, 
  allb f = tt   ↔   Allb f :=
begin
  sorry -- See tutorial04-sol.lean
end


/-
A relation R : X → X → Prop is said to be **decidable** if there is a
boolean-valued function r : X → X → bool which **decides** R:
- **Soundness**: For every x,x':X that r "says are R-related" 
    (r x x' = tt), it is indeed the case that R x x'
- **Completeness**: For every x,x':X that *are* indeed R-related 
    (R x x'), r "detects it", i.e. r x x' = tt   
-/
def Divides (d n : ℕ) : Prop :=
  ∃ q, q * d = n

def divides : ℕ → ℕ → bool := sorry

theorem divides_sound : ∀ d n, divides d n = tt → Divides d n := sorry
theorem divides_complete : ∀ d n, Divides d n → divides d n = tt := sorry

/-
This example would take a lot of work. We'd need to prove a lot of
lemmas (using strong induction), but it is possible
-/
#check nat.case_strong_induction_on

/- 
### Worked example: Inequality of naturals
-/
def Ineq (m n : ℕ) : Prop := m ≠ n

def ineq : ℕ → ℕ → bool
| 0 0 := ff
| 0 (succ n) := tt
| (succ m) 0 := tt
| (succ m) (succ n) := ineq m n   

lemma ineq_irefl : ∀ n, ineq n n ≠ tt :=
begin
  assume n h,
  induction n with n' ih,
  contradiction,
  apply ih,
  exact h, --this computes simply to ineq m n. So makes sense.
end

--Sound means if decider claims that _ then _
theorem ineq_sound : ∀ m n, ineq m n = tt → Ineq m n :=
begin
  assume m n h,
  induction m with m' ih,
  cases n,
  dsimp[Ineq],
  dsimp[ineq] at h,
  contradiction,

  dsimp[Ineq],
  assume absurd,
  contradiction,

  cases n,
  dsimp[Ineq],
  assume f,
  contradiction,

  --injective: f(x) = f(y) → x = y
  --succ(x) = succ(y) → x = y
  assume sm_eq_sn,
  injection sm_eq_sn with m_eq_n,
  rewrite m_eq_n at h,
  apply ineq_irefl,
  exact h,--we already have something of this form!
end 

-- Different way of proving it
  theorem ineq_sound' : ∀ m n, ineq m n = tt → Ineq m n :=
  begin
    assume m,
    induction m with m ih,
    assume n h,
    cases n,
    contradiction,
    assume abs,
    contradiction,
    assume n h,
    cases n,
    contradiction,
    dsimp[ineq] at h,
    assume sm_eq_sn,
    apply ih,
    exact h,
    injection sm_eq_sn,
  end

--
variable P : Prop
lemma efq : false → P :=
begin
  assume f,
  cases f,
end

theorem ineq_complete' : ∀ m n, Ineq m n → ineq m n = tt :=
begin 
  assume m n h,
  induction m with m ih,
  cases n,
  apply efq,
  apply h,
  refl,
  refl,
  cases n,
  refl,
  dsimp[ineq],
  sorry,

  -- We need to assume n within the induction, as then we get a forall n within.
end

theorem ineq_complete : ∀ m n, Ineq m n → ineq m n = tt :=
begin
  sorry
end 






/- 
## Bonus Content: Gauss's Kindergarten Theorem
  ∀ n,  1 + 2 + ... + n = n(n+1)/2
-/

def sumall : ℕ → ℕ 
|  0 := 0
| (succ n) := (succ n)+ sumall n

def div2 : ℕ → ℕ 
|  0 := 0
|  1 := 0
|  (succ (succ n)) := succ(div2 n)

-- Claim: ∀ n : ℕ, sumall n = div2(n * (succ n))

-- Auxiliary function & lemmas: doubling, the inverse of div2
def double : ℕ → ℕ
| 0 := 0
| (succ n) := succ(succ(double n))

lemma double_selfadd : ∀ n : ℕ, double n = n + n :=
begin 
  assume n,
  induction n with n' ih,
  refl,
  dsimp[double],
  rewrite ih,
  dsimp[(+)],
  rewrite succ_add,
end 

-- Lemmas
  lemma div2_add : ∀ m n, div2((double m) + n) = m + div2(n) :=
  begin 
    assume m n,
    induction m with m' ih,
    calc
      div2 (double 0+n)
          = div2 (0+n) : by refl
      ... = div2 n : by rw add_lneutr
      ... = 0+div2 n : by rw add_lneutr,
    calc
      div2 (double (succ m')+n)
          = div2 (succ(succ(double m')) + n) : by refl
      ... = div2 (succ(succ(double m') + n)) : by rw succ_add
      ... = div2 (succ(succ(double m' + n))) : by apply congr_arg div2; apply congr_arg succ; rw succ_add
      ... = succ(div2(double m' + n)) : by refl
      ... = succ(m' + div2 n) : by rw ih
      ... = succ m'+div2 n : by rw succ_add,
  end

  lemma div2_succ : ∀ m n : ℕ, div2(m * succ(succ n)) = m + div2(m * n) :=
  begin 
  assume m n,
  dsimp[mul,add],
  rewrite← add_assoc,
  rewrite← double_selfadd,
  apply div2_add,
  end
--

theorem sumall_closed : ∀ n : ℕ, sumall n = div2(n * (succ n)) :=
begin
  sorry,
end
-- *Sometimes the only way to make your life easier is to temporarily make it harder*

end tutorial06