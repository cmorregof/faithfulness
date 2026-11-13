import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 186

*References:*
- [erdosproblems.com/186](https://www.erdosproblems.com/186)
- [Bo89] Bosznay, Á. P., *On the lower estimation of nonaveraging sets*. Acta Math. Hungar.
  (1989), 155-157.
- [ErSa90] Erdős, P. and Sárközy, A., *On a problem of Straus*. Disorder in physical systems
  (1990), 55-66.
- [PhZa24] Pham, H. T. and Zakharov, D., *Sharp bound for the Erdős–Straus non-averaging set
  problem*. [arXiv:2410.14624](https://arxiv.org/abs/2410.14624) (2024).
-/

section

open Filter Topology

namespace Erdos186

/-- A finite set $A$ of natural numbers is *non-averaging* if no $a \in A$ is the arithmetic mean
of at least two other elements of $A$: there is no $S \subseteq A \setminus \{a\}$ with
$|S| \geq 2$ and $\sum_{x \in S} x = |S| \cdot a$. This agrees with [PhZa24] ("a nonempty subset of
$A$ not containing $a$"), since a single element other than $a$ never has mean $a$. -/
def NonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, 2 ≤ S.card → (∑ x ∈ S, x) ≠ S.card * a
instance (A : Finset ℕ) : Decidable (NonAveraging A) := by
  unfold NonAveraging; infer_instance

/-- $F(N)$ is the maximal size of a non-averaging subset of $\{1, \dots, N\}$. -/
def F (N : ℕ) : ℕ :=
  (((Finset.Icc 1 N).powerset).filter NonAveraging).sup Finset.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card < F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≥ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≥ A.card

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} :
    (A.card ≤ F N) ↔ (F N ≥ A.card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≥ A.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≥ A.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≥ A.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≥ A.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hna : NonAveraging A) (hA : A ⊆ Finset.Icc 1 N), A.card ≤ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hna : NonAveraging A) (hA : A ⊆ Finset.Icc 1 N), A.card ≤ F N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hna : NonAveraging A) (hA : A ⊆ Finset.Icc 1 N), A.card ≤ F N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hna : NonAveraging A) (hA : A ⊆ Finset.Icc 1 N), A.card ≤ F N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hna : NonAveraging A) (hA : A ⊆ Finset.Icc 1 N), A.card ≤ F N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA₀ : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA₀ : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA₀ : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA₀ : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) ↔
    (∀ {N : ℕ} {A : Finset ℕ} (hA₀ : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N > A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), A.card ≤ F N) →
    (∀ {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A), F N ≤ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hna : NonAveraging A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
