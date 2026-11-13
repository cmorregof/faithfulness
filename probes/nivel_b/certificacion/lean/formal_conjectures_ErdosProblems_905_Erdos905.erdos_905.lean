import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Clique
/-!
# Erdős Problem 905

*References:*
- [erdosproblems.com/905](https://www.erdosproblems.com/905)
- [KhNi79] Khadzhiivanov, N. G. and Nikiforov, S. V., *Solution of a problem of P. Erdős about the
  maximum number of triangles with a common edge in a graph*. C. R. Acad. Bulgare Sci. (1979),
  1315-1318.
-/

section

namespace Erdos905

open Finset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 4 ≤ (#G.edgeFinset : ℝ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((n : ℝ) ^ 2 / 5 < (#G.edgeFinset : ℝ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔ (∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e₁ ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e₁) : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG₀ : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 < (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) ≥ (n : ℝ) ^ 2 / 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]  :
    ((n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) ↔ ((#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ)) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4), ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≥ (#(G.trianglesContaining e) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
