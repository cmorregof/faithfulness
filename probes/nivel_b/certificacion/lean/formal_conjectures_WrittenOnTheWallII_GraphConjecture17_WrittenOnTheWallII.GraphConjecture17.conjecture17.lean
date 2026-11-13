import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Written on the Wall II - Conjecture 17

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture17

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ < b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≥ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔ (b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h₀ : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G > (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≥ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 4⌉) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) →
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G) →
    (∀ (G : SimpleGraph α) (h : G.Connected), b G ≤ (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
