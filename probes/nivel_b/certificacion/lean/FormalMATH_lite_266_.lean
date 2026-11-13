import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (13 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (13 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (13 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (11 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (11 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (13 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(13 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(14 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (0 < a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (hb : b > 0) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr₀ : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr₀ : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr₀ : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr₀ : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr₀ : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) :
    (a > 0) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) ↔
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : 0 < a) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(13 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(14 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (a > 0) ↔ (a > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (11 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (13 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(13 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (11 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (11 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (13 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (13 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (12 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (12 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (11 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (11 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(11 : ℝ), (13 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(13 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(13 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(13 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((a > 0) ↔ (a > 1))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (a > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (a > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (a > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (a > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (a > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 0) ↔ (a > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 13)) (a b c : ℕ) (ha : a ≥ 1) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (r = tan (π / 12)) ↔ (r = tan (π / 13)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(-1 : ℝ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(1 : ℝ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((r = tan (π / 12)) ↔ (r = tan (π / 13)))) :=
  ⟨(0 : ℝ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(13 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(14 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((r = tan (π / 12)) ↔ (r = tan (π / 13))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) →
    (∀ (r : ℝ) (hr : r = tan (π / 12)) (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)), a + b + c = 135) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    (b > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (13 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (12 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (11 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (11 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (13 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (13 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (12 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (11 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (12 : ℕ), (13 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (11 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (11 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(11 : ℝ), (13 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (12 : ℕ), (12 : ℕ), (11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (12 : ℕ), (11 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(13 : ℝ), (11 : ℕ), (12 : ℕ), (12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ) (a : ℕ) (b : ℕ) (c : ℕ), (r = tan (π / 12)) ∧ (a > 0) ∧ (c > 0) ∧ (¬∃ p, p.Prime ∧ p ^ 2 ∣ c) ∧ (12 * π * r ^ 2 = π * (a - b * sqrt c)) ∧ (¬((b > 0) ↔ (True))) :=
  ⟨(12 : ℝ), (12 : ℕ), (13 : ℕ), (13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b > 0) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b > 0) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b > 0) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b > 0) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b > 0) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b > 0) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (a b c : ℕ) (hr : r = tan (π / 12)) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hdiv : ¬∃ p, p.Prime ∧ p ^ 2 ∣ c) (hsum : 12 * π * r ^ 2 = π * (a - b * sqrt c)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
