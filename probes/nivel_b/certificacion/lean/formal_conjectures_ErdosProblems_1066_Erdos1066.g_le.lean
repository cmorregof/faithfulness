import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.UnitDistancePlaneGraph
--   import FormalConjecturesForMathlib.Geometry.2d
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 1066

*References:*
- [erdosproblems.com/1066](https://www.erdosproblems.com/1066)
- [Cs98] Csizmadia, G., *On the independence number of minimum distance graphs*.
  Discrete Comput. Geom. 20 (1998), 179-187.
- [Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [PaTo96] Pach, J. and Tóth, G., *On the independence number of coin graphs*.
  Geombinatorics 6 (1996), 30-33.
- [Po85] Pollack, R., *Increasing the minimum distance of a set of points*.
  J. Combin. Theory Ser. A 40 (1985), 450.
- [Sw02] Swanepoel, K. J., *Independence numbers of planar contact graphs*.
  Discrete Comput. Geom. 28 (2002), 649-670.
-/

section

open Filter SimpleGraph
open scoped EuclideanGeometry Topology

namespace Erdos1066

/-- $g(n)$: the largest $m$ such that, for every set $X$ of $n$ points of $\mathbb{R}^2$ with any
two distinct points at distance at least $1$, the graph on $X$ joining points at distance exactly
$1$ has an independent set with at least $m$ vertices. The set of such $m$ contains $0$ and is
bounded by $n$, so `sSup` is a true maximum. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ X : Finset ℝ², X.card = n →
    (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y) →
      m ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card < (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≥ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  omega

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) :
    (g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔ ((UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≥ g X.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX₀ : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX₀ : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX₀ : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX₀ : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) ↔
    (∀ (X : Finset ℝ²) (hX₀ : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum > g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), g X.card ≤ (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum) →
    (∀ (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)), (UnitDistancePlaneGraph (X : Set ℝ²)).indepNum ≤ g X.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y ↦ 1 ≤ dist x y)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
