import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (0 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(17 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(16 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(18 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm₀ : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm₀ : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm₀ : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm₀ : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm₀ : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) ↔
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (a ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(17 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(16 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(18 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < b) ↔ (0 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < b) ↔ (0 ≤ b))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ), ¬((0 < b) ↔ (0 ≤ b)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ), ¬((0 < b) ↔ (0 ≤ b)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ), ¬((0 < b) ↔ (0 ≤ b)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ), ¬((0 < b) ↔ (0 ≤ b)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ), ¬((0 < b) ↔ (0 ≤ b)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ), ¬((0 < b) ↔ (0 ≤ b)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (1 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(17 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(16 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(18 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ), ¬((m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ↔ (m ≠ 4 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℝ} (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (a b c : ℤ) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) →
    (∀ {m : ℝ} (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)), a + b + c = 263) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    (0 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℝ), (2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℝ) (a : ℤ) (b : ℤ) (c : ℤ), (m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) ∧ (3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) ∧ (0 < b) ∧ (0 < c) ∧ (m = a + Real.sqrt (b + Real.sqrt c)) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℝ} (a b c : ℤ) (hm : m ≠ 3 ∧ m ≠ 5 ∧ m ≠ 17 ∧ m ≠ 19) (h : 3 / (m - 3) + 5 / (m - 5) + 17 / (m - 17) + 19 / (m - 19) = m ^ 2 - 11 * m - 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : m = a + Real.sqrt (b + Real.sqrt c)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
