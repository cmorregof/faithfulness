import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Partitions of $n$ into distinct non-squarefree parts for $n > 23$

a: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that
$\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.

*References:*
- [A256012](https://oeis.org/A256012)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA256012

open Nat Finset

/--
a: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that
$\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.
-/
def a (n : ℕ) : ℕ :=
  -- The parts must be $\le n$ to sum to $n$.
  -- This is $\{1, 2, \dots, n\}$
  let potential_parts : Finset ℕ := range (n + 1) \ {0}

  -- We count all subsets P of potential_parts that satisfy the sum and the property.
  card <| filter (fun P : Finset ℕ =>
    P.sum id = n ∧
    (∀ k ∈ P, ¬ Squarefree k)
  ) (powerset potential_parts)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 23), a n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 24), a n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), a n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(25 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(25 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 23 < n), a n > 0

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (23 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : 23 < n), a n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : 23 < n), a n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : 23 < n), a n > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : 23 < n), a n > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), 0 < a n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n > 0) ↔ (0 < a n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n > 23), 0 < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n > 23), 0 < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n > 23), 0 < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n > 23), 0 < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn₀ : n > 23), a n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn₀ : n > 23), a n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn₀ : n > 23), a n > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn₀ : n > 23), a n > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 23)), a n > 0

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (¬(n ≤ 23)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 23)), a n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 23)), a n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 23)), a n > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 23)), a n > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 24), a n > 0

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 23) ↔ (n ≥ 24) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n ≥ 24), a n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n ≥ 24), a n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n ≥ 24), a n > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) ↔
    (∀ (n : ℕ) (hn : n ≥ 24), a n > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 23 ≤ n), a n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 23 ≤ n), a n > 0) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (23 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (23 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (23 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 24 < n), a n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : 24 < n), a n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (24 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(25 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (24 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(25 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (24 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 23), 0 < a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 23), 0 < a n) →
    (∀ (n : ℕ) (hn : n > 23), a n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n ≥ 23) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n ≥ 23))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n ≥ 23)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 23), a n > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 24), 0 < a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 23), a n > 0) →
    (∀ (n : ℕ) (hn : n > 24), 0 < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 23) ↔ (n > 24) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(25 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 23) ↔ (n > 24))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(23 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(24 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(25 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 23) ↔ (n > 24)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 23) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 23) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 23) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 23) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 23) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
