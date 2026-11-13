import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
/-!
# Written on the Wall II - Conjecture 316

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) < (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((averageDegree Gᶜ : ℚ) < (pendantVertices G).card) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card ≥ (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) (hG : G.Connected), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) (hG : G.Connected), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) (hG : G.Connected), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) (hG : G.Connected), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) (hG : G.Connected), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (pendantVertices G).card > (averageDegree Gᶜ : ℚ)), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ ((pendantVertices G).card > (averageDegree Gᶜ : ℚ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ((averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
