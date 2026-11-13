import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set
open scoped BigOperators

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 < a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (1 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (1 < a))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (1 < a))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (1 < a))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (1 < a))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (1 < a)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (1 < a)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (1 < a)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (1 < a)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (1 < a)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (1 < a)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x₁ y z : ℝ, 0 ≤ x₁ ∧ 0 ≤ y ∧ 0 ≤ z ∧ x₁ + y + z = a ∧ t = 2 * x₁ ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha₀ : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha₀ : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha₀ : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha₀ : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha₀ : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : ¬(a < 1)), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℝ) :
    (1 ≤ a) ↔ (¬(a < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : ¬(a < 1)), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : ¬(a < 1)), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : ¬(a < 1)), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔
    (∀ (a : ℝ) (ha : ¬(a < 1)), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a > 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ)  :
    (1 ≤ a) ↔ (a > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (a > 1))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (a > 1))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (a > 1))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (a > 1))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (a > 1))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (¬((1 ≤ a) ↔ (a > 1))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (a > 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (a > 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (a > 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (a > 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (a > 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((1 ≤ a) ↔ (a > 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) →
    (∀ (a : ℝ) (ha : a ≥ 1), IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), (1 ≤ a) ∧ (¬(IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 2 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2)) ↔ (IsGreatest {t | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = a ∧ t = 3 * x ^ 2 + y + 3 * z ^ 2} (3 * a ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a : ℝ) (ha : 1 ≤ a) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a : ℝ) (ha : 1 ≤ a) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (ha : 1 ≤ a) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a : ℝ) (ha : 1 ≤ a) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ) (ha : 1 ≤ a) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
