import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Written on the Wall II - Conjecture 65

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. Start with the path $v_0-v_1-\cdots-v_{12}$ and attach one
triangle at $v_1$ and another at $v_{11}$. The resulting graph has $17$ vertices.
Its Graph_6 string is `PhCGGC@?G?_@?@O?G?G?G?@C`.
Its only minimum-degree vertices are $v_0$ and $v_{12}$, at distance $12$, while its
only maximum-degree vertices are $v_1$ and $v_{11}$, at distance $10$. Thus the
conjectured lower bound is $12 + \lceil 10/3 \rceil = 16$.

Every induced forest must omit at least one vertex from each of the two vertex-disjoint
triangles, so it has at most $15$ vertices. Conversely, deleting one non-path vertex
from each triangle leaves a tree on $15$ vertices.
-/

section

namespace WrittenOnTheWallII.GraphConjecture65

open SimpleGraph Finset

/- Synthesizing `∀ v, Fintype ↥(graph.neighborSet v)` on our 18-edges graph uses more than the
default `synthInstance.maxSize` of 128 instances. That option bounds how many instances a solution
may use, not how long the search may take. Raising it is free -- synthesis costs ~13ms either way
about 1% of this file's elaboration time; the rest is `decide` and kernel type-checking. -/
set_option synthInstance.maxSize 400

namespace Counterexample

/-- The counterexample: a path on vertices $0,\ldots,12$, with triangles attached at
vertices $1$ and $11$. -/
abbrev graph : SimpleGraph (Fin 17) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 6),
    s(6, 7), s(7, 8), s(8, 9), s(9, 10), s(10, 11), s(11, 12),
    s(1, 13), s(1, 14), s(13, 14),
    s(11, 15), s(11, 16), s(15, 16)
  }

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card < 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 16) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≥ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≥ S.card

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  omega

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) :
    (S.card ≤ 15) ↔ (15 ≥ S.card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≥ S.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≥ S.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≥ S.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≥ S.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS₀ : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS₀ : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS₀ : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS₀ : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) ↔
    (∀ (S : Finset (Fin 17)) (hS₀ : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 > S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 16 ≥ S.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), S.card ≤ 15) →
    (∀ (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic), 15 ≤ S.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
