import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 825

*Reference:* [erdosproblems.com/825](https://www.erdosproblems.com/825)
-/

section

open scoped ArithmeticFunction.sigma

namespace Erdos825

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 ≤ C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 ≤ C)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 ≤ C)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 ≤ C)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 ≤ C)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 ≤ C)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 ≤ C)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 3 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(3 < C)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (3 < C)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 > C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(2 > C)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(2 > C)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(2 > C)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(2 > C)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(2 > C)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(2 > C)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 > C)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 > C)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 > C)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 > C)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 > C)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (2 > C)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 2

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (C > 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h₀ : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h₀ : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h₀ : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h₀ : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h₀ : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), ¬(C ≤ 2)

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) :
    (2 < C) ↔ (¬(C ≤ 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), ¬(C ≤ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), ¬(C ≤ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), ¬(C ≤ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) ↔
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), ¬(C ≤ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C ≥ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C ≥ 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C ≥ 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C ≥ 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C ≥ 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C ≥ 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C ≥ 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C > 3) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C > 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C > 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), 2 < C) →
    (∀ (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id), C < 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C < 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C < 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C < 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C < 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C < 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), (∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) ∧ (¬(C < 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C < 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C < 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C < 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C < 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C < 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (C : ℝ), ¬((2 < C) ↔ (C < 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (C : ℝ) (_hC : 0 < C) (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
