import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Conway's 99-graph problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem)
-/

section

namespace Conway99Graph

-- TODO(firsching): Consider using SimpleGraph.IsSRGWith to formulate the conjecture.

open SimpleGraph

variable {V : Type} {G : SimpleGraph V}

variable [Fintype V]

variable [DecidableEq V]
/--
Each two non-adjacent vertices have exactly two common neighbors.
-/
def NonEdgesAreDiagonals (G : SimpleGraph V) : Prop :=
   Pairwise fun i j => ¬ G.Adj i j → (G.neighborSet i ∩ G.neighborSet j).ncard = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  (completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))

set_option maxHeartbeats 200000 in
example : Prop :=
  (completeGraph (Fin 3)).LocallyLinear

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    ((completeGraph (Fin 3)).LocallyLinear) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬(((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ ((completeGraph (Fin 3)).LocallyLinear)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬(((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ ((completeGraph (Fin 3)).LocallyLinear)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  (completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))

set_option maxHeartbeats 200000 in
example : Prop :=
  NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔
    (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔
    (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔
    (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔
    (NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  (completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))

set_option maxHeartbeats 200000 in
example : Prop :=
  NonEdgesAreDiagonals (completeGraph (Fin 3))

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    ((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) →
    (NonEdgesAreDiagonals (completeGraph (Fin 3))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬(((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬(((completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3))) ↔ (NonEdgesAreDiagonals (completeGraph (Fin 3)))) :=
  by decide

#eval "FIN_CERTIFICAR"
