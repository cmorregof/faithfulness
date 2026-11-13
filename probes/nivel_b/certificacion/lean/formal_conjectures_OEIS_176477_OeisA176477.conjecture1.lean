import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Recurrence with fourth powers of binomial coefficients

The sequence is defined by $a(1) = 2$, and for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$

*References:*
- [A176477](https://oeis.org/A176477)
- Z.-W. Sun, "Open Conjectures on Congruences", arXiv preprint
  [arXiv:0911.5665](https://arxiv.org/abs/0911.5665) [math.NT], 2009-2011.
- T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?",
  [arXiv:2608.11941](https://arxiv.org/abs/2608.11941) [cs.AI], 2026.
-/

section

namespace OeisA176477

/-- Rational recurrence sequence $a(n)$. -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let idx : ℚ := n + 2
    let prev := a (n + 1)
    (32 * idx ^ 3 * prev +
      (21 * idx ^ 3 + 22 * idx ^ 2 + 8 * idx + 1) *
        ((2 * (n + 2) - 1).choose (n + 2) : ℚ) ^ 4) /
      (2 * idx + 1) ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 < n), (a n).den = 1 ∧ 0 < a n) := by
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
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 < a n

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
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n ∧ (a n).den = 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n ∧ (a n).den = 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n ∧ (a n).den = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n ∧ (a n).den = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n ∧ (a n).den = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n ∧ (a n).den = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 1)), (a n).den = 1 ∧ 0 < a n

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
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (a n).den = 1 ∧ 0 < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (a n).den = 1 ∧ 0 < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (a n).den = 1 ∧ 0 < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (a n).den = 1 ∧ 0 < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 < a n

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
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n > 1), (a n).den = 1 ∧ 0 < a n) := by
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
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 0 < n), (a n).den = 1 ∧ 0 > a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ ((a n).den = 1 ∧ 0 > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (a n).den = 1 ∧ 0 < a n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), 0 < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n).den = 1 ∧ 0 < a n) ↔ (0 < a n)) :=
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
