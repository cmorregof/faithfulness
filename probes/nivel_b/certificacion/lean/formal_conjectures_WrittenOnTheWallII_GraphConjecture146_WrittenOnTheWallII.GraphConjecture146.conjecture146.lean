import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
/-!
# Written on the Wall II - Conjecture 146

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **square** of a graph $G$, denoted $G^2$, is the graph on the same vertex set
where two distinct vertices are adjacent if and only if their distance in $G$ is at
most $2$.

The **radius of $G^2$** is the minimum eccentricity of any vertex in $G^2$, i.e.,
$$\mathrm{rad}(G^2) = \min_{v \in V} \max_{u \in V} \mathrm{dist}_{G^2}(u, v).$$
-/

section

namespace WrittenOnTheWallII.GraphConjecture146

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The radius of $G^2$ (the graph square): the minimum eccentricity over all vertices
of `graphSquare G`. -/
noncomputable def graphSquareRadius (G : SimpleGraph α) : ℕ :=
  (graphSquare G).radius.toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < graphSquareRadius G) ↔ (graphSquareRadius G > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hrad : 0 < graphSquareRadius G) (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hrad : 0 < graphSquareRadius G) (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hrad : 0 < graphSquareRadius G) (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hrad : 0 < graphSquareRadius G) (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hrad : 0 < graphSquareRadius G) (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : graphSquareRadius G > 0), 3 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G), 2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < graphSquareRadius G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
