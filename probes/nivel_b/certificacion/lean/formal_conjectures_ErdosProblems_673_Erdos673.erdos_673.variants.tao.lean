import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 673

*References:*
- [erdosproblems.com/673](https://www.erdosproblems.com/673)
- [Er79e] Erdős, Paul, _Some unconventional problems in number theory_. Astérisque (1979), 73-82.
- [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_. (1982),
  59--79.
-/

section

open Filter Asymptotics Real

namespace Erdos673

/-- If $1=d_1<\cdots <d_{\tau(n)}=n$ are the divisors of $n$ (here `Nat.nth (· ∣ n) i` is
$d_{i+1}$), then
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$ -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (((n / m).divisors.card : ℝ) / m ≤ G n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : n > 0) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : n > 0) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : n > 0) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : n > 0) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : n > 0) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card ∧ ((n / m).divisors.card : ℝ) / m ≤ G n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn₀ : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn₀ : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn₀ : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn₀ : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn₀ : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : ¬(n ≤ 0)) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : ¬(n ≤ 0)) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : ¬(n ≤ 0)) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : ¬(n ≤ 0)) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : ¬(n ≤ 0)) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (1 ≤ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 1 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hmn : m ∣ n) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (m ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hmn : m ∣ n) :
    (1 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (0 < n) ∧ (m ∣ n) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) →
    (∀ (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n), G n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card) ↔ (G n ≤ n.divisors.card)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
