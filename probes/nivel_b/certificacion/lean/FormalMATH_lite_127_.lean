import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (0 < w) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₁ : w > 0) (h₀ : r = 8) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₁ : w > 0) (h₀ : r = 8) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₁ : w > 0) (h₀ : r = 8) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₁ : w > 0) (h₀ : r = 8) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₁ : w > 0) (h₀ : r = 8) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀' : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀' : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀' : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀' : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀' : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : ¬(w ≤ 0)) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (¬(w ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : ¬(w ≤ 0)) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : ¬(w ≤ 0)) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : ¬(w ≤ 0)) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : ¬(w ≤ 0)) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) :
    (w > 0) ↔ (w ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) ↔
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : 0 < w) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) →
    (∀ (r w : ℕ) (h₀ : r = 9) (h₁ : w ≥ 1) (h₂ : (w + r) * (5 / 6 : ℚ) = w), w = 40) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    (r = 8) ↔ (r = 9) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(0 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(5 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ) (w : ℕ), (w > 0) ∧ ((w + r) * (5 / 6 : ℚ) = w) ∧ (¬((r = 8) ↔ (r = 9))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((r = 8) ↔ (r = 9)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (r w : ℕ) (h₀ : r = 8) (h₁ : w > 0) (h₂ : (w + r) * (5 / 6 : ℚ) = w) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
