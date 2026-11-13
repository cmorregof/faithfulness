import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1033

*References:*
- [erdosproblems.com/1033](https://www.erdosproblems.com/1033)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59--79.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [ErLa85] Erdős, Paul and Laskar, Renu, *A note on the size of a chordal subgraph*.
  Congr. Numer. (1985), 81--86.
- [Fa88] Fan, Genghua, *Degree sum for a triangle in a graph*. J. Graph Theory (1988), 249--263.
-/

section

open Filter Finset

namespace Erdos1033

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 ≤ 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 ≤ 4 * #G.edgeFinset) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 5 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (n ^ 2 < 5 * #G.edgeFinset) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset > n ^ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔ (∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t₁, G.IsNClique 3 t₁ ∧ 21 * n ≤ 16 * ∑ v ∈ t₁, G.degree v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n < 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset ≥ n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (4 * #G.edgeFinset ≥ n ^ 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 5 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    (n ^ 2 < 4 * #G.edgeFinset) ↔ (5 * #G.edgeFinset > n ^ 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset), ∃ t, G.IsNClique 3 t ∧ 21 * n ≤ 16 * ∑ v ∈ t, G.degree v) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : 4 * #G.edgeFinset > n ^ 2), ∃ t, G.IsNClique 3 t ∧ 21 * n ≥ 16 * ∑ v ∈ t, G.degree v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : n ^ 2 < 4 * #G.edgeFinset) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
