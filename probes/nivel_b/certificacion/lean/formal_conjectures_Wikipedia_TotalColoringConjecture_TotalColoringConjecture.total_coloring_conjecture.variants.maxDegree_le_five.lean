import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.TotalColouring
/-!
# The total colouring conjecture (Behzad 1965, Vizing 1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Total_coloring)
* [Be65] Behzad, M. (1965). *Graphs and their chromatic numbers.* Ph.D. thesis, Michigan State
  University.
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [Ko96] Kostochka, A. V. (1996). "The total chromatic number of any multigraph with maximum
  degree five is at most seven." *Discrete Math.* 162, pp. 199--214.
* [MR98] Molloy, M. and Reed, B. (1998). "A bound on the total chromatic number."
  *Combinatorica* 18, pp. 241--280.
* [Yap96] Yap, H. P. (1996). *Total colourings of graphs.* Lecture Notes in Mathematics 1623,
  Springer.
-/

section

open SimpleGraph

namespace TotalColoringConjecture

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree ≤ 5) ↔ (5 ≥ G.maxDegree) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.maxDegree + 2 ≥ G.totalChromaticNumber

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.totalChromaticNumber ≤ G.maxDegree + 2) ↔ (G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ₀ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ₀ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ₀ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ₀ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ₀ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 5 > G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (5 > G.maxDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : 6 ≥ G.maxDegree), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (6 ≥ G.maxDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree < 5), G.maxDegree + 2 ≥ G.totalChromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree < 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 6), G.maxDegree + 2 ≥ G.totalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5), G.totalChromaticNumber ≤ G.maxDegree + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    (G.maxDegree ≤ 5) ↔ (G.maxDegree ≤ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
