import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Matching
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree
/-!
# Written on the Wall II - Conjecture 1

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture1

open SimpleGraph

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22 u_c23 u_c24 u_c25
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c2} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G < (Ls G : ℝ)) →
    (∀ {α : Type u_c1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c4} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c5} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) →
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c7} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c8} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≥ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c10} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c11} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  omega

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {α : Type u_c12} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ((Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔ ((Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c10} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c11} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c10} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c11} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c10} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c11} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c10} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c11} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c13} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c14} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn₀ : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c13} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c14} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn₀ : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c13} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c14} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn₀ : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c13} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c14} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn₀ : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c13} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) ↔
    (∀ {α : Type u_c14} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn₀ : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c17} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) > (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c16} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) →
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c19} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c20} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≥ (Fintype.card α : ℝ) + 1 - 3 * matchingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) →
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : Type u_c22} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ)) →
    (∀ {α : Type u_c23} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected), (Ls G : ℝ) ≤ (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : Type u_c25} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {α : Type u_c25} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {α : Type u_c25} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {α : Type u_c25} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : Type u_c25} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
