import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey
/-!
# Erdős Problem 557

*References:*
- [erdosproblems.com/557](https://www.erdosproblems.com/557)
- [ErGr75] Erdős, P. and Graham, R. L., *On partition theorems for finite graphs*. Infinite and
  finite sets (Colloq., Keszthely, 1973), Vol. I, Colloq. Math. Soc. János Bolyai 10 (1975),
  515-527.
- [ReSt26] Reed, Bruce and Stein, Maya, *The Erdős-Sós conjecture in dense graphs*.
  [arXiv:2609.05417](https://arxiv.org/abs/2609.05417) (2026).
-/

section

open SimpleGraph

namespace Erdos557

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 3) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≥ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔ (k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≥ multicolourGraphRamsey k T) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT₀ : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT₀ : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT₀ : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT₀ : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) ↔
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT₀ : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 3) + 3 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 3) →
    (∀ (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 3 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
