import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (5 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(3 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(5 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(5 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 < 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (3 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (5 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(3 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(5 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(5 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 7)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (3 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (5 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(3 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(5 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(5 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≥ 6)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h₀ : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h₀ : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h₀ : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h₀ : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h₀ : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), ¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), ¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), ¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), ¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), ¬(6 < (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 > (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (7 ≥ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) →
    (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), 6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (a^2 + b^2 + c^2 + d^2 = 1) ∧ (¬(6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (3 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (5 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (4 : ℝ), (5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(3 : ℝ), (5 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (4 : ℝ), (3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(5 : ℝ), (3 : ℝ), (4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬(((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6) ↔ (6 ≤ (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4)) :=
  ⟨(4 : ℝ), (4 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
