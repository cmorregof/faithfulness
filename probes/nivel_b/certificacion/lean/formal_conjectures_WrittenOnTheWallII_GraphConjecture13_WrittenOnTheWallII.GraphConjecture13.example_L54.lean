import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Written on the Wall II - Conjecture 13

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture13

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

-- Sanity checks

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 < b G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 < b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≥ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), b G ≥ 0

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) :
    (0 ≤ b G) ↔ (b G ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) ↔
    (∀ (G : SimpleGraph (Fin 3)), b G ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) ↔
    (∀ (G : SimpleGraph (Fin 3)), b G ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) ↔
    (∀ (G : SimpleGraph (Fin 3)), b G ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) ↔
    (∀ (G : SimpleGraph (Fin 3)), b G ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), b G > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G > 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)), b G ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) →
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)), 0 ≤ b G) →
    (∀ (G : SimpleGraph (Fin 3)), b G ≤ 0) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
