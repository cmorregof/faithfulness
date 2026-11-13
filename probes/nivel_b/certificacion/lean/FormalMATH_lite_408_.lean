import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set
open scoped Real

set_option maxHeartbeats 200000 in
example : Prop :=
  (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬(((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬(((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  (cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬(((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬(((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ ((cos (25 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1 ∧ (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  (cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    ((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) →
    (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬(((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬(((cos (24 * π / 180))^2 + (sin (6 * π / 180))^2 + (cos (18 * π / 180))^2 = 7 / 4 ∧ 4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1) ↔ (4 * (cos (36 * π / 180))^2 - sin (84 * π / 180) * (sqrt 3 - tan (6 * π / 180)) = 1)) :=
  by decide

#eval "FIN_CERTIFICAR"
