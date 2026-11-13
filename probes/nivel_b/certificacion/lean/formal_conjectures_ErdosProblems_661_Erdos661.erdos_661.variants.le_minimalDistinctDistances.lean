import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.Metric
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 661

*References:*
- [erdosproblems.com/661](https://www.erdosproblems.com/661)
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
  Combinatorica (1990), 261--269.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*.
  Eureka (1992), 44-48.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [Er46] Erdős, Paul, *On sets of distances of $n$ points*. Amer. Math. Monthly 53 (1946),
  248--250.
-/

section

open Filter Finset EuclideanGeometry

namespace Erdos661

variable {X : Type*} [MetricSpace X]

/-- The set of distances $d(x, y)$ with $x \in A$ and $y \in B$. -/
noncomputable def crossDistanceSet (A B : Finset X) : Finset ℝ :=
  (A ×ˢ B).image fun p : X × X => dist p.1 p.2

variable (X) in
/-- The minimal number of distinct distances $d(x_i, y_j)$ over all choices of $2n$ distinct
points $x_1, \ldots, x_n, y_1, \ldots, y_n$ in `X`.

The $x_i$ form a set `A` of $n$ points, the $y_j$ form a set `B` of $n$ points, and `A` and `B`
are disjoint, so all $2n$ points are distinct. -/
noncomputable def minimalCrossDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B ∧
    #(crossDistanceSet A B) = m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n < minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (3 * n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalCrossDistances ℝ² n ≥ minimalDistinctDistances ℝ² (2 * n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≥ minimalCrossDistances ℝ² n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), ¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), ¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), ¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔
    (∀ (n : ℕ), ¬(minimalDistinctDistances ℝ² (2 * n) < minimalCrossDistances ℝ² n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) > minimalCrossDistances ℝ² n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (3 * n) ≥ minimalCrossDistances ℝ² n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) →
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) →
    (∀ (n : ℕ), minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n)) ↔ (minimalDistinctDistances ℝ² (2 * n) ≤ minimalCrossDistances ℝ² n)) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
