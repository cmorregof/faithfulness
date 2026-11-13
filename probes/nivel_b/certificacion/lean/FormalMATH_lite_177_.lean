import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53001 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  omega

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  simp_all

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ}  :
    (P = fun t => 53000 + 2100 * t) ↔ (P = fun t => 53001 + 2100 * t) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000 ∧ P (-530 / 21) = 0

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  omega

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} :
    (P (-530 / 21) = 0 ∧ P 0 = 53000) ↔ (P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000 ∧ P (-530 / 21) = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP₀ : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP₀ : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP₀ : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP₀ : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) ↔
    (∀ {P : ℝ → ℝ} (hP₀ : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P (-530 / 21) = 0 ∧ P 0 = 53000) →
    (∀ {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t), P 0 = 53000) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {P : ℝ → ℝ} (hP : P = fun t => 53000 + 2100 * t) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
