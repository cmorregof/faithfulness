import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 311

*References:*
- [erdosproblems.com/311](https://www.erdosproblems.com/311)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980), p. 40.
-/

section

namespace Erdos311

open Finset Filter Topology

/--
`delta N` is the minimal non-zero value of $\lvert 1-\sum_{n\in A}\frac{1}{n}\rvert$ as $A$
ranges over all subsets of $\{1,\ldots,N\}$. The empty set gives the value $1$, so the set
below is nonempty for every $N$.
-/
noncomputable def delta (N : ℕ) : ℝ :=
  sInf {x : ℝ | x ≠ 0 ∧ ∃ A ⊆ Icc 1 N, x = |1 - ∑ n ∈ A, (1 : ℝ) / n|}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) < delta N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≥ delta N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), delta N ≥ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), ¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), ¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), ¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), ¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔
    (∀ (N : ℕ), ¬(delta N < 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N > 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) →
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) →
    (∀ (N : ℕ), delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬(delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N) ↔ (delta N ≤ 1 / (((Icc 1 N).lcm id : ℕ) : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
