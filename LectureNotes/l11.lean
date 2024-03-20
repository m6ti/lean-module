namespace l11
set_option pp.structure_projections false
open nat

def double : ℕ → ℕ 
| zero := zero
| (succ m) := succ (succ (double m))

def half : ℕ → ℕ 
| zero := zero
| (succ zero) := zero
| (succ (succ m)) := succ (half m)

example : ∀ n : ℕ, half (double n) = n :=
begin
  assume n,
  induction n with n' ih,
  dsimp [double, half],
  reflexivity,
  dsimp [double],
  dsimp [half],
  rewrite ih,
end

---

def add : ℕ → ℕ → ℕ 
| n zero := n
| n (succ m) := succ (add n m)

local notation  m + n := add m n

#eval 3 + 5

def mult : ℕ → ℕ → ℕ 
| n zero := zero
| n (succ m) := mult n m + n

local notation  m * n := mult m n

#eval 3 * 5

-- define exponentiation

-- algebra

theorem lneutr : ∀ n : ℕ, 0 + n = n :=
begin
 assume n,
 induction n with n' ih,
 dsimp [(+),add],
 reflexivity,
 dsimp [(+),add],
 rewrite ih,
end

theorem rneutr : ∀ n : ℕ, n + 0 = n :=
begin
  assume n,
  dsimp [(+),add],
  reflexivity
end

theorem assoc : ∀ l m n : ℕ, 
    (l + m) + n = l + (m + n) :=
begin
  assume l m n,
  induction n with n' ih,
  dsimp [(+),add],
  reflexivity,
  dsimp [(+),add],
  rewrite ih,
end   







-- Quick recap :)
lemma add_succ2 : ∀ m n : ℕ,
  (succ m) + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  dsimp[(+)],
  refl,
  dsimp[(+)],
  rewrite ih,
end



-- lneutr+rneutr+assoc = monoid

lemma add_succ : ∀ m n : ℕ,
  (succ m) + n = succ (m + n) :=
begin
  assume m n,
  induction n with n' ih,
  dsimp [(+),add],
  reflexivity,
  dsimp [(+),add],
  rewrite ih,
end

theorem comm : ∀ m n : ℕ , m + n = n + m :=
begin
  assume m n,
  induction n with n' ih,
  dsimp [(+),add],
  rewrite lneutr,
  dsimp [(+),add],
  rewrite add_succ,
  rewrite ih,
end

-- monoid + comm = commutative monoid

end l11

