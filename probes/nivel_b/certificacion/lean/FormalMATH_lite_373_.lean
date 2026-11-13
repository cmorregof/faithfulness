import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha₀ : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha₀ : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha₀ : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha₀ : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha₀ : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : ¬(a < 0)) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) :
    (0 ≤ a) ↔ (¬(a < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : ¬(a < 0)) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : ¬(a < 0)) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : ¬(a < 0)) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔
    (∀ (a b c d : ℝ) (ha : ¬(a < 0)) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c < 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a > 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (a > 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (a > 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (a > 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (a > 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (a > 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (a > 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (a > 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (a > 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 28 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (b * c * d + c * d * a + d * a * b + a * b * c ≥ 1 / 27 + 176 / 27 * a * b * c * d)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d > b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ a) ↔ (0 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ a) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 ≤ a) ↔ (0 < a)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 28 + 176 / 27 * a * b * c * d ≥ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), 1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬(1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), ¬((b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) ↔ (1 / 27 + 176 / 27 * a * b * c * d ≤ b * c * d + c * d * a + d * a * b + a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) →
    (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1), b * c * d + c * d * a + d * a * b + a * b * c ≤ 1 / 27 + 176 / 27 * a * b * c * d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    (0 ≤ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ), (0 ≤ a) ∧ (0 ≤ c) ∧ (0 ≤ d) ∧ (a + b + c + d = 1) ∧ (¬((0 ≤ b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 ≤ b) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 ≤ b) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 ≤ b) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 ≤ b) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 ≤ b) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 ≤ b) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a + b + c + d = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
