import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.UnitDistancePlaneGraph
/-!
# Erdős Problem 1007

*References:*
- [erdosproblems.com/1007](https://www.erdosproblems.com/1007)
- [ChNo16] Chaffee, Joe and Noble, Matt, *Dimension 4 and dimension 5 graphs with minimum edge
  set*. Australas. J. Combin. (2016), 327-333.
- [Ho13] House, Roger F., *A 4-dimensional graph has at least 9 edges*. Discrete Math. (2013),
  1783-1789.
-/

section

namespace Erdos1007

open scoped EuclideanGeometry

variable {V : Type*}

/-- The complete tripartite graph $K_{1,3,3}$. -/
abbrev K133 := SimpleGraph.completeMultipartiteGraph fun i : Fin 3 => Fin (![1, 3, 3] i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example : Prop :=
  ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example : Prop :=
  ((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ (((SimpleGraph.completeGraph (Fin 6)).HasDimension 6 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example : Prop :=
  (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15) ∧ ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example : Prop :=
  (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) →
    ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((((SimpleGraph.completeGraph (Fin 6)).HasDimension 5 ∧
        (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15) ∧
      (K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15)) ↔ ((K133.HasDimension 5 ∧ K133.edgeSet.ncard = 15))) :=
  by decide

#eval "FIN_CERTIFICAR"
