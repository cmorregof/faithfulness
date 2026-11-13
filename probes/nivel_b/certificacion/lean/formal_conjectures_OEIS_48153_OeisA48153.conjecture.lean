import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# $a(n) = \sum_{k=1}^n (k^2 \bmod n)$

*References:*
- [A048153](https://oeis.org/A048153)-/

section

namespace OeisA48153

/-- $a(n) = \sum_{k=1}^n (k^2 \bmod n)$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (k ^ 2 % n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≥ a n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≥ a n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≥ a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≥ a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≥ a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≥ a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 1)), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), a n ≤ (n ^ 2 - 1) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), a n ≤ (n ^ 2 - 1) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) ↔
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n > 1), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 < n), (n ^ 2 - 1) / 2 ≥ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 3 ≥ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 3 ≥ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n ^ 2 - 1) / 2 ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ ((n ^ 2 - 1) / 2 ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n < (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n < (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n < (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≤ (n ^ 2 - 1) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≤ (n ^ 2 - 1) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≤ (n ^ 2 - 1) / 2) →
    (∀ (n : ℕ) (hn : 0 < n), a n ≥ (n ^ 2 - 1) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n ≤ (n ^ 2 - 1) / 2) ↔ (a n ≥ (n ^ 2 - 1) / 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
