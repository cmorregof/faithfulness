import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 ≥ 0)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 < 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (a * b + b * c + c * a + 1 < 0)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 < a * b + b * c + c * a + 1

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (0 < a * b + b * c + c * a + 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 < a * b + b * c + c * a + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 < a * b + b * c + c * a + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 < a * b + b * c + c * a + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 < a * b + b * c + c * a + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : |b| < 1) (ha : |a| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (hb : |b| < 1) (ha : |a| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (hb : |b| < 1) (ha : |a| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (hb : |b| < 1) (ha : |a| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (hb : |b| < 1) (ha : |a| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha₀ : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha₀ : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha₀ : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha₀ : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha₀ : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), ¬(a * b + b * c + c * a + 1 ≤ 0)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b + b * c + c * a + 1 > 0) ↔ (¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), ¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), ¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), ¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) ↔
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), ¬(a * b + b * c + c * a + 1 ≤ 0)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 ≤ a * b + b * c + c * a + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 ≤ a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), a * b + b * c + c * a + 1 > 0) →
    (∀ (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1), 0 > a * b + b * c + c * a + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (|a| < 1) ∧ (|b| < 1) ∧ (|c| < 1) ∧ (¬(0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b + b * c + c * a + 1 > 0) ↔ (0 > a * b + b * c + c * a + 1)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
