import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced
/-!
# Written on the Wall II - Conjecture 198a

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture198a

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G < 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G < 2 + averageEccentricity G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 3 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (b G ≤ 3 + averageEccentricity G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G ≥ b G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (hb : b G ≤ 2 + averageEccentricity G) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (hb : b G ≤ 2 + averageEccentricity G) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (hb : b G ≤ 2 + averageEccentricity G) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (hb : b G ≤ 2 + averageEccentricity G) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (hb : b G ≤ 2 + averageEccentricity G) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h₀ : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) (h₀ : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 2 + averageEccentricity G > b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (2 + averageEccentricity G > b G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : 3 + averageEccentricity G ≥ b G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (3 + averageEccentricity G ≥ b G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) :
    (b G ≤ 2 + averageEccentricity G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (h : G.Connected) (hb : b G ≤ 2 + averageEccentricity G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
