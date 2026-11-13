import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Goldbach's conjecture

*References:*
- [Landau Problems Wikipedia Page](https://en.wikipedia.org/wiki/Landau%27s_problems#Twin_prime_conjecture)
- [Goldbach's Conjecture Wikipedia Page](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture)
-/

section

namespace GoldbachConjecture

end GoldbachConjecture

namespace TernaryGoldbachConjecture

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (5 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (5 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (5 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 6 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (6 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (6 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (6 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (n > 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : n > 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : n > 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : n > 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : n > 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔ (∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p₁ q r, Nat.Prime p₁ ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p₁ + q + r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn_odd : Odd n) (hn : 5 < n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn_odd : Odd n) (hn : 5 < n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn_odd : Odd n) (hn : 5 < n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn_odd : Odd n) (hn : 5 < n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn_odd : Odd n) (hn : 5 < n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn₀ : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn₀ : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn₀ : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn₀ : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 5)) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (¬(n ≤ 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 5)) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 5)) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 5)) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 5)) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 6 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 < n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 6 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 6 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 6 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) ↔
    (∀ (n : ℕ) (hn : 6 ≤ n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 5) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n ≥ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n ≥ 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n ≥ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 < n) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) →
    (∀ (n : ℕ) (hn : n > 6) (hn_odd : Odd n), ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_odd : Odd n) :
    (5 < n) ↔ (n > 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((5 < n) ↔ (n > 6))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 < n) ↔ (n > 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 < n) (hn_odd : Odd n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 < n) (hn_odd : Odd n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 < n) (hn_odd : Odd n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 < n) (hn_odd : Odd n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 < n) (hn_odd : Odd n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
