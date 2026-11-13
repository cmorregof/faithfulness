import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a ≥ 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (a ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₁ < 1)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 < a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (1 < a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : 1 < a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : 1 < a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : 1 < a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : 1 < a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1 ∧ x₁ < 1

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1 ∧ x₁ < 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1 ∧ x₁ < 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1 ∧ x₁ < 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1 ∧ x₁ < 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1 ∧ x₁ < 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha₀ : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha₀ : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha₀ : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha₀ : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha₀ : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : ¬(a ≤ 1)) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : ¬(a ≤ 1)) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : ¬(a ≤ 1)) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : ¬(a ≤ 1)) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) ↔
    (∀ (a : ℝ) (ha : ¬(a ≤ 1)) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : 1 ≤ a) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (1 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (x₁ x₂ : ℝ) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    (a > 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (x₁ : ℝ) (x₂ : ℝ), ((a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) ∧ ((a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) ∧ (x₁ > 0) ∧ (x₂ < 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₁ < 1 ∧ x₂ > -1) →
    (∀ (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0), x₂ > -1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x₁ : ℝ) (x₂ : ℝ), ¬((x₁ < 1 ∧ x₂ > -1) ↔ (x₂ > -1)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (ha : a > 1) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (ha : a > 1) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (ha : a > 1) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (ha : a > 1) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℝ) (x₁ x₂ : ℝ) (ha : a > 1) (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2)) (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
