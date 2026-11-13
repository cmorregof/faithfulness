import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(3 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(1/2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (a + b = 3)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 3 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) :
    (logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), (2 ^ b + b - 3 = 0) ∧ (¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0))) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((logb 2 a + a - 3 = 0) ↔ (logb 3 a + a - 3 = 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) (ha : logb 2 a + a - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) (ha : logb 2 a + a - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) (ha : logb 2 a + a - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) (ha : logb 2 a + a - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (hb : 2 ^ b + b - 3 = 0) (ha : logb 2 a + a - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3 ∧ a + b = 3

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b : ℝ} :
    (a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3 ∧ a + b = 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha₀ : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha₀ : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha₀ : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha₀ : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔
    (∀ {a b : ℝ} (ha₀ : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), a + b = 3 ∧ logb 2 a + 2 ^ b = 3) →
    (∀ {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0), logb 2 a + 2 ^ b = 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(3 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(1/2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ), ¬((a + b = 3 ∧ logb 2 a + 2 ^ b = 3) ↔ (logb 2 a + 2 ^ b = 3)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b : ℝ} (ha : logb 2 a + a - 3 = 0) (hb : 2 ^ b + b - 3 = 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
