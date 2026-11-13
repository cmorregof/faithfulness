import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 131

*References:*
- [erdosproblems.com/131](https://www.erdosproblems.com/131)
- [ELRSS99] Erdős, P. and Lev, V. and Rauzy, G. and Sándor, C. and Sárközy, A., *Greedy
  algorithm, arithmetic progressions, subset sums and divisibility*. Discrete Math. (1999),
  119-135.
- [PhZa24] Pham, H. T. and Zakharov, D., *Sharp bound for the Erdős–Straus non-averaging set
  problem*. [arXiv:2410.14624](https://arxiv.org/abs/2410.14624) (2024).
-/

section

open Filter Topology

namespace Erdos131

/-- A finite set $A$ of naturals is *non-dividing* if no $a \in A$ divides the sum of the
elements of any nonempty subset $S \subseteq A \setminus \{a\}$. -/
def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S.Nonempty → ¬ a ∣ ∑ x ∈ S, x
instance (A : Finset ℕ) : Decidable (NonDividing A) := by
  unfold NonDividing; infer_instance

/-- $F(N)$ is the maximal size of a non-dividing subset of $\{1, \dots, N\}$. -/
def F (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonDividing).sup Finset.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) ≤ 3 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) ≤ 3 * Real.sqrt N + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 4 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) < 4 * Real.sqrt N + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), (F N : ℝ) > 3 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ ((F N : ℝ) > 3 * Real.sqrt N + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 3 * Real.sqrt N + 1 > (F N : ℝ)

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 > (F N : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), ¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), ¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), ¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), ¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) ↔
    (∀ (N : ℕ), ¬(3 * Real.sqrt N + 1 ≤ (F N : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 ≥ (F N : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 ≥ (F N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 4 * Real.sqrt N + 1 > (F N : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (4 * Real.sqrt N + 1 > (F N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) →
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (F N : ℝ) < 3 * Real.sqrt N + 1) →
    (∀ (N : ℕ), 3 * Real.sqrt N + 1 < (F N : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((F N : ℝ) < 3 * Real.sqrt N + 1) ↔ (3 * Real.sqrt N + 1 < (F N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
