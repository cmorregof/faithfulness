import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Temperature
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree
/-!
# Written on the Wall II - Conjecture 3

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

universe u

namespace WrittenOnTheWallII.GraphConjecture3

open SimpleGraph

variable {α : Type u} [Fintype α] [DecidableEq α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G < Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≥ Ls G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≥ G.indepDominationNumber * MaxTemp G

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] :
    (G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔ (Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≥ G.indepDominationNumber * MaxTemp G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn₀ : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn₀ : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn₀ : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn₀ : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) ↔
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn₀ : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G > G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), G.indepDominationNumber * MaxTemp G ≤ Ls G) →
    (∀ {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected), Ls G ≤ G.indepDominationNumber * MaxTemp G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {G : SimpleGraph α} [DecidableRel G.Adj] [Nontrivial α] (h_conn : G.Connected) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
