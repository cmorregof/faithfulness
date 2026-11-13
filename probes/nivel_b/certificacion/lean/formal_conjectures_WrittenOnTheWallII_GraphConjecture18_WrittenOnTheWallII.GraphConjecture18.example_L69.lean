import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
/-!
# Written on the Wall II - Conjecture 18

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture18

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

-- Sanity checks

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 < distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≥ distToSet G v S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≥ 0

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) :
    (0 ≤ distToSet G v S) ↔ (distToSet G v S ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S > 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), 0 ≤ distToSet G v S) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)), distToSet G v S ≤ 0) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
