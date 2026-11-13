import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set
open scoped BigOperators

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 3 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ}  :
    (f = λ x => (x - 1) / (x^2 - 2 * x + 5)) ↔ (f = λ x => (x - 1) / (x^2 - 3 * x + 5)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} :
    (IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔ (IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17) ∧ IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf₀ : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsGreatest (image f (Icc (3 / 2) 2)) (1 / 5) ∧
    IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) →
    (∀ {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)), IsLeast (image f (Icc (3 / 2) 2)) (2 / 17)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (hf : f = λ x => (x - 1) / (x^2 - 2 * x + 5)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
