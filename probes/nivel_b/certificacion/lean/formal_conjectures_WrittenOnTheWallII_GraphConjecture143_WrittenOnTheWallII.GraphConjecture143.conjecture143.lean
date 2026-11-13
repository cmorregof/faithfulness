import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
/-!
# Written on the Wall II - Conjecture 143

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture143

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (0 < secondSmallestDegree G) ↔ (secondSmallestDegree G > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔ ((largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≥ (G.girth : ℝ) + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hσ : 0 < secondSmallestDegree G) (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hσ : 0 < secondSmallestDegree G) (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hσ : 0 < secondSmallestDegree G) (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hσ : 0 < secondSmallestDegree G) (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hσ : 0 < secondSmallestDegree G) (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 < (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : secondSmallestDegree G > 0), (G.girth : ℝ) + 1 ≥ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) > (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) ≤ (G.girth : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G), (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (0 < secondSmallestDegree G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hσ : 0 < secondSmallestDegree G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
