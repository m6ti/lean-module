variables P Q R :Prop
variables A B C :Type
variables PP QQ :A → Prop
variables RR :A → A → Prop

example : (∀ x : A , PP x) → (∀ x : A, PP x → QQ x)
  → ∀ x : A, QQ x :=
begin
  assume pp ppqq,
  assume george,
  apply ppqq,
  apply pp,
end

/-example : (∀ x: A, PP x ∧ QQ x)
↔ (∀ x : A, PP x) ∧ (∀ x : A , QQ x) :=
begin
  constructor,
  assume ppnqq,
  constructor,
  assume george,
  
/-Revise this!!!-/  
end
-/


example : (∃ x: A, PP x)
→ (∀ x : A, PP x → QQ x) →  ∃ x : A , QQ x :=
begin
  assume pp ppqq,
  cases pp with a pa,
  constructor,
  apply ppqq,
  apply pa,
end

example : (∃ x: A, PP x)
→ (∀ x : A, PP x → QQ x) →  ∃ x : A , QQ x :=
begin
  assume pp ppqq,
  cases pp with a pa,
  existsi a,
  apply ppqq,
  apply pa,
end

/- 
  To prove ∃ x: A , PP x we say existi a, 
  where a:A and we have to prove PP a
  
  to use h: ∃ x:A, PPx we say cases h with a ppa,
  and we have two assumptions, a: A and ppa : PP a
-/

example : (∃ x: A, PP x ∨ QQ x)
↔ (∃ x : A, PP x) ∨ (∃ x : A , QQ x) :=

begin 
  constructor,
  assume h,
  cases h with a ppqqa,
  cases ppqqa with ppa qqa,
  left,
  existsi a,
  apply ppa,
  right,
  existsi a,
  assumption, --nice one
  
  assume h,
  cases h with pp qq,
  cases pp with a ppa,
  existsi a,
  left,
  assumption,

  cases qq with a qqa,
  existsi a,
  right, 
  assumption,
end

/- 
  a b : A
  a = b : Prop

  =: A → A → Prop

  how to prove an equality
  how to use an assumed equality.
-/

example : ∀ x : A, x = x :=
begin 
  assume a,
  reflexivity,
end

example : ∀ x y : A, x = y → PP y -> PP x :=
begin 
  assume a b,
  assume ab ppa,
  rewrite ab,
  apply ppa,
end

/- 

  a :b : A
  a = b : Prop

  =: A -> A -> Prop

  we can prove a = a,
  by reflexivity

  how to use as assumed equality
  if we know h:a = b
  we say rewrite h,
  and we have to prove PP b.


-/


example : ∀ x y : A, x=y → PP x → PP y:=
begin 
  assume a b,
  assume ab ppa,
  rewrite ← ab,
  assumption,
end
-- equality s symettric,

example : ∀ x y : A , x = y → y = x :=
begin
  assume x y,
  assume xy,
  rewrite xy,
end
-- ORRRRR:
example : ∀ x y : A , x = y → y = x :=
begin
  assume a b ab,
  rewrite ab,
end

example : ∀ x y z : A, x = y → y = z → x = z :=
begin
  assume a b c ab bc,
  rewrite← bc,
  assumption,
end

-- reflexive , symettric and transitive
-- equivalence relation...

