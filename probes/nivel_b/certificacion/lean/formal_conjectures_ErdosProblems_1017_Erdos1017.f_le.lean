import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Chordal
/-!
# Erdős Problem 1017

*References:*
- [erdosproblems.com/1017](https://www.erdosproblems.com/1017)
- [EGP66] Erdős, Paul and Goodman, A. W. and Pósa, Lajos,
  *The representation of a graph by set intersections*. Canadian J. Math. (1966), 106–112.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
- [GyKe17] Győri, Ervin and Keszegh, Balázs,
  *On the number of edge-disjoint triangles in $K_4$-free graphs*.
  Combinatorica (2017), 1113–1124.
- [Lo68] Lovász, L., *On covering of graphs*.
  Theory of Graphs (Proc. Colloq., Tihany, 1966) (1968), 231–236.
-/

section

namespace Erdos1017

open SimpleGraph

/-- The least uniform bound on the number of cliques in an edge partition of an
$n$-vertex, $k$-edge graph. For infeasible parameters the value is zero. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = k →
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧ P.card ≤ m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k < k

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k < k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k < k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k < k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≥ k

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≥ k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), f n k ≥ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(f n k ≥ k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (f n k ≥ k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), k ≥ f n k

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (k ≥ f n k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), k ≥ f n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), k ≥ f n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), k ≥ f n k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), k ≥ f n k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), ¬(k < f n k)

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (f n k ≤ k) ↔ (¬(k < f n k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), ¬(k < f n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), ¬(k < f n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), ¬(k < f n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) ↔
    (∀ (n k : ℕ), ¬(k < f n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), k > f n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k > f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k > f n k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k > f n k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), f n k ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ), k ≤ f n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), k ≤ f n k) →
    (∀ (n k : ℕ), f n k ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ), f n k ≤ k) →
    (∀ (n k : ℕ), k ≤ f n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬(k ≤ f n k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((f n k ≤ k) ↔ (k ≤ f n k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
