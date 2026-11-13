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
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≥ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : N ≥ 1), 1 ≤ F N

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≤ F N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≤ F N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≤ F N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≤ F N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), F N ≥ 1

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ F N) ↔ (F N ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≥ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≥ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN₀ : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), 1 ≤ F N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), 1 ≤ F N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), 1 ≤ F N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), 1 ≤ F N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : ¬(N < 1)), 1 ≤ F N

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), 1 ≤ F N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), 1 ≤ F N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), 1 ≤ F N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), 1 ≤ F N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 0 < N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 0 < N), 1 ≤ F N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 0 < N), 1 ≤ F N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 0 < N), 1 ≤ F N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) ↔
    (∀ {N : ℕ} (hN : 0 < N), 1 ≤ F N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : N ≥ 1), 1 < F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : N > 1), 1 ≤ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N > 1), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : N ≥ 1), 1 ≥ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), F N > 1

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N > 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 < N), F N ≥ 1

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 < N), F N ≥ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), F N ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N ≤ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N ≤ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N ≤ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N ≤ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N ≤ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(F N ≤ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N ≤ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N ≤ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N ≤ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N ≤ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N ≤ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (F N ≤ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 0 < N), 1 < F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 < F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 < F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 < F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) →
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), 1 ≤ F N) →
    (∀ {N : ℕ} (hN : 0 < N), 1 ≥ F N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(1 ≥ F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ F N) ↔ (1 ≥ F N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
