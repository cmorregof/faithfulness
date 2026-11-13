import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.Metric
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 1087

*References:*
- [erdosproblems.com/1087](https://www.erdosproblems.com/1087)
- [ErPu71] Erdős, P. and Purdy, G., *Some extremal problems in geometry*. J. Combinatorial Theory
  Ser. A 10 (1971), 246-252.
-/

section

open Filter Asymptotics
open scoped EuclideanGeometry

namespace Erdos1087

/-- A finite set of points has a repeated distance if two of its pairs of points are the same
distance apart, that is, if it determines fewer distinct distances than it has pairs. -/
def HasRepeatedDistance (S : Finset ℝ²) : Prop :=
  distinctDistances S < S.card.choose 2

open scoped Classical in
/-- The number of degenerate four-element subsets of `P`, that is, those in which two of the six
pairwise distances are equal. -/
noncomputable def degenerateCount (P : Finset ℝ²) : ℕ :=
  ((P.powersetCard 4).filter HasRepeatedDistance).card

/-- $f(n)$: the maximum, over all sets of $n$ points in the plane, of the number of degenerate
four-element subsets. The set of values is nonempty and bounded by $\binom{n}{4}$, so `sSup` is
a true maximum. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ degenerateCount P = m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P < f P.card

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P < f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), degenerateCount P ≥ f P.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), f P.card ≥ degenerateCount P

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  omega

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (P : Finset ℝ²) :
    (degenerateCount P ≤ f P.card) ↔ (f P.card ≥ degenerateCount P) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) ↔
    (∀ (P : Finset ℝ²), f P.card ≥ degenerateCount P) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) ↔
    (∀ (P : Finset ℝ²), f P.card ≥ degenerateCount P) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) ↔
    (∀ (P : Finset ℝ²), f P.card ≥ degenerateCount P) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) ↔
    (∀ (P : Finset ℝ²), f P.card ≥ degenerateCount P) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), f P.card > degenerateCount P

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card > degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) →
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (P : Finset ℝ²), degenerateCount P ≤ f P.card) →
    (∀ (P : Finset ℝ²), f P.card ≤ degenerateCount P) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
