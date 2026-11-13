import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) (ha_pos : 0 < a), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (True) ↔ (0 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (0 ≤ t - 4) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((True) ↔ (0 < a))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((True) ↔ (0 < a)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((True) ↔ (0 < a)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((True) ↔ (0 < a)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((True) ↔ (0 < a)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((True) ↔ (0 < a)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((True) ↔ (0 < a)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha₀ : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha₀ : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha₀ : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha₀ : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha₀ : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : ¬(t < 0)) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : ¬(t < 0)) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : ¬(t < 0)) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : ¬(t < 0)) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) ↔
    (∀ (a b c t : ℝ) (ha : ¬(t < 0)) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 5) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (0 ≤ t - 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (0 ≤ t - 5))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (0 ≤ t - 5)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (ha : t ≥ 0) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) →
    (∀ (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2), a = 52) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    (0 ≤ t - 4) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ) (b : ℝ) (c : ℝ) (t : ℝ), (0 ≤ t) ∧ (0 ≤ t - 2) ∧ (6 * t = a) ∧ (6 * (t - 2) + 4 * (t - 2) = b) ∧ (8 * (t - 4) = c) ∧ (a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) ∧ (¬((0 ≤ t - 4) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t - 4) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4) (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c) (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
