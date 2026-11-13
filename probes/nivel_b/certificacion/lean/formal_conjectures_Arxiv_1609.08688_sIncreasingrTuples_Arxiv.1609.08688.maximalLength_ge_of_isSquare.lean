import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The length of an $s$-increasing sequence of $r$-tuples

This file contains the formalisation of [GoLo21] up to and
including Conjecture 1.8.

*References:*
- [arxiv/1609.08688](https://arxiv.org/abs/1609.08688)
  **The length of an $s$-increasing sequence of $r$-tuples** by *W. T. Gowers, J. Long*
- [GoLo21](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/length-of-an-sincreasing-sequence-of-rtuples/7301418D47DB1ECD6BE71C20E8A98D0A)
  **The length of an $s$-increasing sequence of $r$-tuples**
  by *W. T. Gowers, J. Long*, Combinatorics, Probability and Computing (2021), 686-721
-/

section

namespace Arxiv.«1609.08688»

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two coordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 < F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 < F n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 < F n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≥ F n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(n.sqrt ^ 3 ≥ F n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (n.sqrt ^ 3 ≥ F n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), F n ≥ n.sqrt ^ 3

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (F n ≥ n.sqrt ^ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), F n ≥ n.sqrt ^ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), F n ≥ n.sqrt ^ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), F n ≥ n.sqrt ^ 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), F n ≥ n.sqrt ^ 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h₀ : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h₀ : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h₀ : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h₀ : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h₀ : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), ¬(F n < n.sqrt ^ 3)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n.sqrt ^ 3 ≤ F n) ↔ (¬(F n < n.sqrt ^ 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), ¬(F n < n.sqrt ^ 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), ¬(F n < n.sqrt ^ 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), ¬(F n < n.sqrt ^ 3)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) ↔
    (∀ {n : ℕ} (h : IsSquare n), ¬(F n < n.sqrt ^ 3)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n > n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n > n.sqrt ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n > n.sqrt ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) →
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : IsSquare n), n.sqrt ^ 3 ≤ F n) →
    (∀ {n : ℕ} (h : IsSquare n), F n ≤ n.sqrt ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (IsSquare n) ∧ (¬(F n ≤ n.sqrt ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n.sqrt ^ 3 ≤ F n) ↔ (F n ≤ n.sqrt ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : IsSquare n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : IsSquare n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : IsSquare n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : IsSquare n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : IsSquare n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
