import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    (b ≠ a * c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((b ≠ a * c) ↔ (True)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 5 * b ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : ¬(b = a * c)) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) :
    (b ≠ a * c) ↔ (¬(b = a * c)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb : ¬(b = a * c)) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb : ¬(b = a * c)) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb : ¬(b = a * c)) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb : ¬(b = a * c)) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ≠ -c) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (ha : a ≠ -c) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (ha : a ≠ -c) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (ha : a ≠ -c) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (ha : a ≠ -c) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb₀ : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb₀ : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb₀ : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb₀ : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) ↔
    (∀ (a b c : ℝ) (hb₀ : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) →
    (∀ (a b c : ℝ) (hb : b ≠ a * c) (ha : a ≠ -c) (z : ℂ) (hz : z^2 - (a - c) * z - b = 0), Complex.abs ((a^2 + b - (a + c) * z) / (a * c - b)) = 1 ↔ (a - c)^2 + 4 * b ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (hz : z^2 - (a - c) * z - b = 0) :
    (a ≠ -c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (c : ℝ), ¬((a ≠ -c) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (z : ℂ) (hb : b ≠ a * c) (ha : a ≠ -c) (hz : z^2 - (a - c) * z - b = 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
