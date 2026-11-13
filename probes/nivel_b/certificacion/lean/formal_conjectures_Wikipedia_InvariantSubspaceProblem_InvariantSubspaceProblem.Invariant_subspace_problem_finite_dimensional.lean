import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Invariant Subspace Problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Invariant_subspace_problem),
[Chalendar-Partington](https://arxiv.org/abs/2507.21834)
-/

section

namespace InvariantSubspaceProblem

variable {H : Type*} [NormedAddCommGroup H]

/-- `ClosedInvariantSubspace T` is the type of non-trivial (different from `H` and `{0}`) closed
subspaces of a complex vector space `H` that are invariant under the action of linear map `T`. -/
structure ClosedInvariantSubspace [Module ℂ H] (T : H →L[ℂ] H) where
  toSubspace : Submodule ℂ H
  ne_bot : toSubspace ≠ ⊥
  ne_top : toSubspace ≠ ⊤
  is_closed : IsClosed (toSubspace : Set H)
  is_fixed : toSubspace.map T.toLinearMap ≤ toSubspace

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 < Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H) := by
  plausible

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (2 < Module.rank ℂ H)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 3 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H) := by
  plausible

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (3 ≤ Module.rank ℂ H)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (hdim : 2 ≤ Module.rank ℂ H) (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (hdim : 2 ≤ Module.rank ℂ H) (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (hdim : 2 ≤ Module.rank ℂ H) (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (hdim : 2 ≤ Module.rank ℂ H) (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (hdim : 2 ≤ Module.rank ℂ H) (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h₀ : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h₀ : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h₀ : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h₀ : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h₀ : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : ¬(Module.rank ℂ H < 2)) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) :
    (2 ≤ Module.rank ℂ H) ↔ (¬(Module.rank ℂ H < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : ¬(Module.rank ℂ H < 2)) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : ¬(Module.rank ℂ H < 2)) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : ¬(Module.rank ℂ H < 2)) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) ↔
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : ¬(Module.rank ℂ H < 2)) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H > 2) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H > 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : Module.rank ℂ H ≥ 3) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (Module.rank ℂ H ≥ 3)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) →
    (∀ [NormedSpace ℂ H] (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H), Nonempty (ClosedInvariantSubspace T)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) :
    (2 ≤ Module.rank ℂ H) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (FiniteDimensional ℂ H) ∧ (¬((2 ≤ Module.rank ℂ H) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((2 ≤ Module.rank ℂ H) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example [NormedSpace ℂ H] (T : H →L[ℂ] H) (h : FiniteDimensional ℂ H) (hdim : 2 ≤ Module.rank ℂ H) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
