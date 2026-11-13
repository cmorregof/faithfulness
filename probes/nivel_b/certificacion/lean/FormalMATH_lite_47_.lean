import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set
open scoped Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (2 * θ)) / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (2 * θ)) / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (2 * θ)) / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (2 * θ)) / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (2 * θ)) / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (2 * θ)) / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), (¬(sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (sin θ^2 = (1 - cos (3 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  omega

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {θ : ℝ} :
    (sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2 ∧ sin θ^2 = (1 - cos (2 * θ)) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {θ : ℝ}, sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) →
    (∀ {θ : ℝ}, cos θ^2 = (1 + cos (2 * θ)) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((sin θ^2 = (1 - cos (2 * θ)) / 2 ∧ cos θ^2 = (1 + cos (2 * θ)) / 2) ↔ (cos θ^2 = (1 + cos (2 * θ)) / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

#eval "FIN_CERTIFICAR"
