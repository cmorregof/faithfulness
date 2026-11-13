import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.ZMod.PerfectDifferenceSet
/-!
# Erdős Problem 707: Embedding Sidon Sets in Perfect Difference Sets

*References:*
- [erdosproblems.com/707](https://www.erdosproblems.com/707)
- [arxiv/2510.19804](https://arxiv.org/abs/2510.19804) Boris Alexeev and Dustin G. Mixon, Forbidden
  Sidon subsets of perfect difference sets, featuring a human-assisted proof (2025)
- [Ha47] Marshall Hall, Jr., Cyclic projective planes, Duke Math. J. 14 (1947), 1079–1090.

Let `A ⊆ ℕ` be a finite Sidon set. Is there some set `B` with `A ⊆ B` which is a perfect
difference set modulo `p^2 + p + 1` for some prime power `p`?

This problem is related to Erdős Problem 329 about the maximum density of Sidon sets.
If this conjecture is true, it would imply that the maximum density of Sidon sets is 1.
-/

section

open Function Set

namespace Erdos707

/-  ## Perfect difference sets and their properties -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard < n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≥ n.sqrt + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≥ B.ncard

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  omega

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) :
    (B.ncard ≤ n.sqrt + 1) ↔ (n.sqrt + 1 ≥ B.ncard) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≥ B.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≥ B.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≥ B.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≥ B.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB₀ : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB₀ : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB₀ : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB₀ : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) ↔
    (∀ (B : Set ℕ) (n : ℕ) (hB₀ : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 > B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), B.ncard ≤ n.sqrt + 1) →
    (∀ (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n), n.sqrt + 1 ≤ B.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSet B n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
