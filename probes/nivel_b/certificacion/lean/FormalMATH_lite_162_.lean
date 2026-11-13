import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 ≤ x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (0 ≤ x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (0 ≤ x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (0 ≤ x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (0 ≤ x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (0 ≤ x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (0 ≤ x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (0 ≤ x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (28 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (28 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (27 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (27 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(27 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (26 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (27 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (27 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (26 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (27 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (27 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0₁ y0 z0 : ℝ, 0 < x0₁ ∧ 0 < y0 ∧ 0 < z0 ∧ x0₁ * y0 + z0 = (x0₁ + z0) * (y0 + z0) ∧ x0₁ * y0 * z0 = 1 / 27) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hypos : 0 < y) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hypos : 0 < y) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hypos : 0 < y) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hypos : 0 < y) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hypos : 0 < y) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos₀ : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos₀ : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos₀ : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos₀ : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos₀ : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : ¬(x ≤ 0)) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : ¬(x ≤ 0)) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : ¬(x ≤ 0)) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : ¬(x ≤ 0)) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔
    (∀ (x y z : ℝ) (hxpos : ¬(x ≤ 0)) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x ≥ 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < x) ↔ (x ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (x ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (x ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (x ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (x ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (x ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((0 < x) ↔ (x ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : x > 0) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (28 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (28 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < y) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬(x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (27 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (27 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(27 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (1 : ℝ), (26 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (0 : ℝ), (27 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (27 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(1 : ℝ), (26 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (1 : ℝ), (27 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(0 : ℝ), (27 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), ¬((x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) ↔ (x * y * z ≤ 1 / 28 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) →
    (∀ (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)), x * y * z ≤ 1 / 27 ∧
    ∃ x0 y0 z0 : ℝ, 0 < x0 ∧ 0 < y0 ∧ 0 < z0 ∧ x0 * y0 + z0 = (x0 + z0) * (y0 + z0) ∧ x0 * y0 * z0 = 1 / 27) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    (0 < y) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (0 < x) ∧ (0 < z) ∧ (x * y + z = (x + z) * (y + z)) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((0 < y) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((0 < y) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((0 < y) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((0 < y) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((0 < y) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((0 < y) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y z : ℝ) (hxpos : 0 < x) (hypos : 0 < y) (hzpos : 0 < z) (hxyz : x * y + z = (x + z) * (y + z)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
