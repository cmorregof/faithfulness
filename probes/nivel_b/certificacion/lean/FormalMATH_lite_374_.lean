import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c ≥ a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(2 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c ≥ a + b + c - 2)) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c < a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(2 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a * b * c < a + b + c - 2)) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (a + b + c - 2 < a * b * c) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (ha : a ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (ha : a ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (ha : a ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (ha : a ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (ha : a ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha₀ : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha₀ : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha₀ : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha₀ : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha₀ : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), ¬(a * b * c ≤ a + b + c - 2)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (a * b * c > a + b + c - 2) ↔ (¬(a * b * c ≤ a + b + c - 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), ¬(a * b * c ≤ a + b + c - 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), ¬(a * b * c ≤ a + b + c - 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), ¬(a * b * c ≤ a + b + c - 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) ↔
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), ¬(a * b * c ≤ a + b + c - 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 ≤ a * b * c) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(2 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 ≤ a * b * c)) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-3) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 < a * b * c) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    (a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(2 : ℝ), (4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1))) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a ∈ Set.Ioo (-2) 1) ↔ (a ∈ Set.Ioo (-3) 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a * b * c > a + b + c - 2) →
    (∀ (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1), a + b + c - 2 > a * b * c) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (a ∈ Set.Ioo (-2) 1) ∧ (b ∈ Set.Ioo (-2) 1) ∧ (c ∈ Set.Ioo (-2) 1) ∧ (¬(a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(2 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a * b * c > a + b + c - 2) ↔ (a + b + c - 2 > a * b * c)) :=
  ⟨(3 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : a ∈ Set.Ioo (-2) 1) (hb : b ∈ Set.Ioo (-2) 1) (hc : c ∈ Set.Ioo (-2) 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
