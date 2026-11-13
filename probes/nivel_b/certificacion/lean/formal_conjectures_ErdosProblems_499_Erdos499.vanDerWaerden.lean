import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 499
*Reference:* [erdosproblems.com/499](https://www.erdosproblems.com/499)
-/

section

open Nat

namespace Erdos499

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! < M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≥ M.permanent) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≥ n ^ (- n : ℤ) * n !

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔ (M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≥ n ^ (- n : ℤ) * n !) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM₀ : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM₀ : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM₀ : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM₀ : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) ↔
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM₀ : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent > n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), n ^ (- n : ℤ) * n ! ≤ M.permanent) →
    (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)), M.permanent ≤ n ^ (- n : ℤ) * n !) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
