/-
COMP2065-IFR Exercise 02
-/

namespace poker

variables P Q R : Prop

inductive PokerAnswer : Type
| UNANSWERED : PokerAnswer 
| NotProvable : PokerAnswer
| Intuition : PokerAnswer
| Classical : PokerAnswer
open PokerAnswer

open classical 

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

/- --- Do not add/change anything above this line --- -/

/-
We play the game of logic poker :-)

  You have to classify each proposition as either
  a) provable intuitionistically (i.e. in plain lean)
  b) provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P).
  c) not provable classically.
  and then you have to prove the propositions in a) and b) accordingly.

  You will start with a score of 10 points, and then 1 point will be deducted
  for each incorrect classification and 1 point will be deducted for each
  incorrect proof. We stop deducting at zero, so you cannot earn negative points.
  So, for instance, if you do every proof correctly but do not classify anything,
  you will earn 0/10.
-/

/-
CLASSIFICATION: For each proposition, replace UNANSWERED with
  Intuition     if the proposition is provable intuitionistically (i.e. in plain lean)
  Classical     if the proposition is provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P)
  NotProvable   if the proposition is not provable classically

**Important**: Every classification should be one of these three, or UNANSWERED. 
DO NOT put anything else on the right-hand side or leave it totally blank.

Examples:                                  -/
-- q00 : P → P
def answer00 : PokerAnswer := Intuition

-- q00' : ¬¬P → P
def answer00' : PokerAnswer := Classical

-- q00'' : false
def answer00'' : PokerAnswer := NotProvable

/-
PROOFS: 
  Then, prove the propositions you classified as 'Intuition' or 'Classical'. 
  For the 'Classical' ones, you may use em or raa, as discussed in lecture.
  For propositions classified as 'NotProvable' just keep "sorry," as the proof.

  You are only allowed to use the tactics introduced in the lecture
  (e.g. assume, exact, apply, constructor, cases, left, right, have),

  Please only use the tactics in the way indicated in the lecture notes,
  otherwise we may deduct points.
-/


-- q01 : (P → Q) → (R → P) → (R → Q)
def answer01 : PokerAnswer  := Intuition
theorem q01 : (P → Q) → (R → P) → (R → Q) := 
begin
  assume pq rp r,
  apply pq,
  apply rp,
  exact r,
end

-- q02 : (P → Q) → (P → R) → (Q → R)
def answer02 : PokerAnswer  := NotProvable
theorem q02 : (P → Q) → (P → R) → (Q → R) :=
begin
  sorry, 
end

-- q03 : (P → Q) → (Q → R) → (P → R)
def answer03 : PokerAnswer  := Intuition
theorem q03 : (P → Q) → (Q → R) → (P → R) :=
begin
  assume pq qr p,
  apply qr,
  apply pq,
  exact p,
end

-- q04 : P → (P → Q) → P ∧ Q
def answer04 : PokerAnswer  := Intuition
theorem q04 : P → (P → Q) → P ∧ Q :=
begin
  assume p pq,
  constructor,
  exact p,
  apply pq,
  exact p,
end

-- q05 : P ∨ Q → (P → Q) → Q
def answer05 : PokerAnswer  := Intuition
theorem q05 : P ∨ Q → (P → Q) → Q :=
begin
  assume poq,
  cases poq with p q,
  assume pq,
  apply pq,
  assumption,
  assume pq,
  assumption,
end

-- q06 : (P → Q) → ¬ P ∨ Q
def answer06 : PokerAnswer  := Classical
theorem q06 : (P → Q) → ¬ P ∨ Q :=
begin
  assume pq,
  cases em P with p np,
  right,
  apply pq,
  exact p,
  left,
  exact np,
end

-- q07 : (¬ P ∨ Q) → P → Q
--      CLASSICAL???
def answer07 : PokerAnswer  := Intuition
theorem q07 : (¬ P ∨ Q) → P →   Q :=
begin
  assume npq p,
  cases npq with np q,
  have f: false,
  apply np,
  exact p,
  cases f,
  exact q,
end

-- q08 : ¬ (P ↔ ¬ P)
def answer08 : PokerAnswer  := Classical
theorem q08 : ¬ (P ↔ ¬ P) :=
begin
  assume h,
  cases em P with p np,
  cases h with h1 h2,
  apply h1,
  exact p,
  exact p,
  cases h with h1 h2,
  apply h1,
  apply h2,
  exact np,
  apply h2,
  exact np,
end

-- q09 : ¬ P ↔ ¬ ¬ ¬ P
def answer09 : PokerAnswer  := Intuition
theorem q09 : ¬ P ↔ ¬ ¬ ¬ P :=
begin
  constructor,
  assume np,
  assume nnp,
  apply nnp,
  exact np,
  assume nnnp,
  assume p,
  apply nnnp,
  assume nnp,
  apply nnp,
  exact p,
end

-- q10 : ((P → Q) → P) → P
def answer10 : PokerAnswer  := Classical
theorem q10 : ((P → Q) → P) → P :=
begin
  assume pqp,
  cases em P with p np,
  exact p,
  apply pqp,
  assume p,
  cases em Q with q nq,
  exact q,
  have f: false,
  apply np,
  exact p,
  cases f,
end

--- Do not add/change anything below this line ---
end poker