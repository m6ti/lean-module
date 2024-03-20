open classical

variables A B C : Type

variables P Q R : Prop

variables PP QQ : A → Prop

example : (∃ x: A, PP x ∨ QQ x) ↔ (∃ x: A, PP x) ∨ (∃ x : A, QQ x):=
begin
  constructor,
  assume ppqq,
  cases ppqq with a pq,
  cases pq with pa qa,
  left,
  existsi a,
  assumption,
  right,
  existsi a,
  assumption,
  assume h,
  cases h with hp hq,
  cases hp with a pa,
  existsi a,
  left,
  assumption,
  cases hq with a qa,
  existsi a,
  right,
  assumption,
end


theorem curry_pred : (∃ x : A, PP x) → R  ↔ (∀ x : A , PP x → R)  :=
begin
  constructor,
  assume h1,
  assume a,
  assume ppa,
  apply h1,
  existsi a,
  assumption,

  assume h2,
  assume h3,
  cases h3 with a ppa,
  apply h2,
  assumption,
end



example : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  transitivity,
  apply xy,
  exact yz,
end
example : ∀ x y : A, x=y → y=x :=
begin
  assume x y xy,
  symmetry,
  assumption,
end

example : ∀ x y z : A, x=y → y=z → x=z :=
begin
  assume x y z xy yz,
  calc
    x = y   : by exact xy
    ... = z : by exact yz,
end



theorem dm1_pred : ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x :=
begin
  constructor,
  assume h1,
  assume a,
  assume ppa,
  apply h1,
  existsi a,
  assumption,
  assume h2,
  assume h3,
  cases h3 with a ppa,
  apply h2,
  apply ppa,
end

theorem raa : ¬ ¬ P → P := 
begin
  assume nnp,
  cases (em P) with p np,
    exact p,
    have f : false,
      apply nnp,
      exact np,
    cases f,
end

theorem dm2_pred : ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x :=
begin
  constructor,
  assume h1,
  apply raa,
  assume h2,
  apply h1,
  assume a,
  apply raa,
  assume nppa,
  apply h2,
  existsi a,
  exact nppa,
  assume h3,
  assume h4,
  cases h3 with a nppa,
  apply nppa,
  apply h4,
end

def is_tt : bool → Prop
| ff := false
| tt := true

theorem cons : tt ≠ ff :=
begin
  assume h,
  change is_tt ff,
  rewrite ← h,
  trivial,
end

theorem distr_b : ∀ x y z : bool,
  x && (y || z) = x && y || x && z :=
begin
  assume x y z,
  cases z,

end


theorem dm1_b : ∀ x y : bool, bnot (x || y) = bnot x && bnot y :=
begin
  assume x y,
  cases y,
  cases x,
  refl,
  refl,
  cases x,
  refl,
  refl,
end

theorem dm2_b : ∀ x y : bool, bnot (x && y) = bnot x || bnot y :=
begin
  assume x y,
  cases x, 
  cases y,
  refl,
  refl,
  cases y,
  refl,
  refl,
end

theorem and_thm : ∀ x y : bool, is_tt x ∧ is_tt y ↔ is_tt (x && y) :=
begin
  assume x y,
  constructor,
  assume h1,
  cases h1 with l r,
  cases x,
  cases l,
  cases y,
  cases r,
  constructor,
  --This can simplify proof so much. Get the right order.
  assume h2,
  cases x,
  cases h2,
  cases y,
  cases h2,
  constructor,
  constructor,
  constructor,
end

theorem not_thm : ∀ x : bool, ¬ (is_tt x) ↔ is_tt (bnot x) :=
begin
  assume x,
  constructor,
  assume nx,
  cases x,
  constructor,
  dsimp[is_tt] at nx,
  dsimp[is_tt,bnot],
  apply nx,
  constructor,

  cases x,
  assume h,
  dsimp[is_tt],
  assume h,
  cases h,
  
  assume h2,
  dsimp[is_tt,bnot] at h2,
  cases h2,
  
end

theorem or_thm : ∀ x y : bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  assume x y,
  constructor,
  assume h2,
  cases h2,
  cases x,
  cases h2,
  dsimp[is_tt,bor],
  constructor,
  cases x,
  cases y,
  cases h2,
  dsimp[is_tt,bor],
  constructor,
  dsimp[is_tt,bor],
  constructor,
  

  assume h1,
  cases x,
  right,
  cases y,
  cases h1,
  assumption,


  dsimp[is_tt,bor] at h1,
  left,
  constructor,
end



