import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 307

*Reference:* [erdosproblems.com/307](https://www.erdosproblems.com/307)
-/

section

namespace Erdos307

open scoped Finset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 < #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 61 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≥ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 60

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  omega

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} :
    (60 ≤ #(P ∪ Q)) ↔ (#(P ∪ Q) ≥ 60) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 60) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 60) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 60) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 60) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (hP : ∀ p ∈ P, p.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP₀ : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP₀ : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP₀ : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP₀ : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) ↔
    (∀ {P Q : Finset ℕ} (hP₀ : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) > 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≥ 61) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), 60 ≤ #(P ∪ Q)) →
    (∀ {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)), #(P ∪ Q) ≤ 60) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
