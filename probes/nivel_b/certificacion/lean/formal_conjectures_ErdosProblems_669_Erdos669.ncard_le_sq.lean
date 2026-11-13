import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.2d
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 669

*References:*
- [erdosproblems.com/669](https://www.erdosproblems.com/669)
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
-/

section

open Filter
open scoped Topology EuclideanGeometry

namespace Erdos669

/--
The set of lines in $\mathbb{R}^2$ containing at least $k$ points of $S$. It is the analogue of
`EuclideanGeometry.linesWithPointsFor`, which asks for exactly $k$ points. Only lines spanned by two
distinct points of $S$ are counted, so the definition is meant for $k \geq 2$.
-/
noncomputable def linesWithAtLeastPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | k ≤ (↑L ∩ S).ncard }

/--
The set of numbers of distinct lines through at least $k$ points, taken over all sets of $n$
points in $\mathbb{R}^2$.
-/
noncomputable def lineCountsAtLeast (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧ (linesWithAtLeastPointsFor k (S : Set ℝ²)).ncard = m}

/--
The set of numbers of distinct lines through exactly $k$ points, taken over all sets of $n$
points in $\mathbb{R}^2$.
-/
noncomputable def lineCountsExactly (k n : ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℝ², S.card = n ∧
    (EuclideanGeometry.linesWithPointsFor k (S : Set ℝ²)).ncard = m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard < S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≥ S.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≥ T.ncard

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  omega

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) :
    (T.ncard ≤ S.card ^ 2) ↔ (S.card ^ 2 ≥ T.ncard) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≥ T.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≥ T.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≥ T.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≥ T.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT₀ : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT₀ : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT₀ : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT₀ : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) ↔
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT₀ : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 > T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), T.ncard ≤ S.card ^ 2) →
    (∀ (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L), S.card ^ 2 ≤ T.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (S : Finset ℝ²) (T : Set (AffineSubspace ℝ ℝ²)) (hT : ∀ L ∈ T, ∃ p ∈ S, ∃ q ∈ S, affineSpan ℝ {p, q} = L) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
