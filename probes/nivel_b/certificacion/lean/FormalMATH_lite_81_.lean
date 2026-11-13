import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 > (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  omega

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 3 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≤ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  omega

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) :
    (x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔ ((x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx₀ : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx₀ : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx₀ : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx₀ : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) ↔
    (∀ (x : Fin 3 → ℝ) (hx₀ : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) < x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  omega

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ)  :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 3 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≤ x 0 * x 1 * x 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), x 0 * x 1 * x 2 ≥ (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2)) →
    (∀ (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i), (x 1 + x 2 - x 0) * (x 0 + x 2 - x 1) * (x 0 + x 1 - x 2) ≥ x 0 * x 1 * x 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : Fin 3 → ℝ) (hx : ∀ i, 0 < x i) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
