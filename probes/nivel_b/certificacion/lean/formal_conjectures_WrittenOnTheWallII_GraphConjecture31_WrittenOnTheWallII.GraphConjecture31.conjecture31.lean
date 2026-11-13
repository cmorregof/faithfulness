import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Written on the Wall II - Conjecture 31

The WOWII page records this as **Chung's theorem**. This radius bound is proved
in Section 2 of P. Erdős, M. Saks, and V. T. Sós, *Maximum Induced Trees in
Graphs*, J. Combin. Theory Ser. B **41** (1986), 61–79; the authors credit
Fan Chung for the proof. We state it here as a theorem; the formal proof is left
as `sorry` pending a Lean port of the argument.

Here $\mathrm{path}(G)$ is the maximum number of vertices in an induced path,
and $\mathrm{rad}(G)$ is the graph radius.

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [P. Erdős, M. Saks, V. T. Sós, Maximum Induced Trees in Graphs](https://doi.org/10.1016/0095-8956(86)90028-6)
-/

section

namespace WrittenOnTheWallII.GraphConjecture31

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 < (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 3 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≥ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔ ((path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 2 * (G.radius.toNat : ℤ) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) > 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≥ 3 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), 2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), (path G : ℤ) ≤ 2 * (G.radius.toNat : ℤ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
