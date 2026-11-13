import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (0 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (7 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (7 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (6 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (7 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (7 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (7 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (3 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (7 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(3 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (7 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (2 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (5 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (7 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (3 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (6 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (7 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔
    (∀ (a b c : ℝ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < a) ↔ (a ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c > a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬((a + b + c ≥ a * b * c) ↔ (a + b + c > a * b * c)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (7 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (7 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(0 : ℝ), (6 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(-1 : ℝ), (7 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (7 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (7 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (3 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (7 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(3 : ℝ), (6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (6 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (7 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(6 : ℝ), (2 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (6 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (5 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (7 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(5 : ℝ), (3 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (6 : ℝ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), ¬(((6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) ↔ ((7 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2))) :=
  ⟨(7 : ℝ), (7 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) →
    (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c), (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / b + 3 / c + 2 / a ≥ 2) ∨
    (6 / a + 3 / b + 2 / c ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2) ∨
    (6 / b + 3 / c + 2 / a ≥ 2 ∧ 6 / c + 3 / a + 2 / b ≥ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    (0 < b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ), (0 < a) ∧ (0 < c) ∧ (a + b + c ≥ a * b * c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 < b) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 < b) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 < b) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 < b) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 < b) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((0 < b) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
