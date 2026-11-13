import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1168

*References:*
* [erdosproblems.com/1168](https://www.erdosproblems.com/1168)
* [EHR65] Erdős, P., Hajnal, A. and Rado, R., *Partition relations for cardinal numbers*.
  Acta Math. Acad. Sci. Hungar. (1965), pp. 93–196.
-/

section

open Cardinal Ordinal SimpleGraph

namespace Erdos1168

namespace erdos_1168.variants

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω ≤ ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω ≤ ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ ω ≤ ℵ_ (ω + 1))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ ω ≤ ℵ_ (ω + 1))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω > ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω > ℵ_ (ω + 1)) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ ω > ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(ℵ_ ω > ℵ_ (ω + 1))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(ℵ_ ω > ℵ_ (ω + 1))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ ω > ℵ_ (ω + 1))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ ω > ℵ_ (ω + 1))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ (ω + 1) > ℵ_ ω

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > ℵ_ ω) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (ℵ_ (ω + 1) > ℵ_ ω) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (ℵ_ (ω + 1) > ℵ_ ω) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (ℵ_ (ω + 1) > ℵ_ ω) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (ℵ_ (ω + 1) > ℵ_ ω) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(ℵ_ (ω + 1) ≤ ℵ_ ω)

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔ (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) ↔
    (¬(ℵ_ (ω + 1) ≤ ℵ_ ω)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ (ω + 1) ≥ ℵ_ ω

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) ≥ ℵ_ ω) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) ≥ ℵ_ ω)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) ≥ ℵ_ ω)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ ω < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ℵ_ (ω + 1) < ℵ_ ω

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ (ω + 1) < ℵ_ ω) →
    (ℵ_ ω < ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (ℵ_ ω < ℵ_ (ω + 1)) →
    (ℵ_ (ω + 1) < ℵ_ ω) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(ℵ_ (ω + 1) < ℵ_ ω)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(ℵ_ (ω + 1) < ℵ_ ω)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) < ℵ_ ω)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ ω < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) < ℵ_ ω)) :=
  by decide

#eval "FIN_CERTIFICAR"
