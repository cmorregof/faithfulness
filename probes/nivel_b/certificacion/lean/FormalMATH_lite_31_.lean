import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set
open scoped BigOperators

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (0 ≤ c1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (0 ≤ c1))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (0 ≤ c1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (0 ≤ c1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (0 ≤ c1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (0 ≤ c1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (0 ≤ c1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (0 ≤ c1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (c1 > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1' : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1' : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1' : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1' : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1' : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : ¬(c1 ≤ 0)) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} :
    (0 < c1) ↔ (¬(c1 ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : ¬(c1 ≤ 0)) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : ¬(c1 ≤ 0)) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : ¬(c1 ≤ 0)) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : ¬(c1 ≤ 0)) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 ≥ 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c1) ↔ (c1 ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c1) ↔ (c1 ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (c1 ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (c1 ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (c1 ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (c1 ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (c1 ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ), ¬((0 < c1) ↔ (c1 ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : c1 > 0) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < c2) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬(let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), ¬((let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) ↔ (let p1 := (u1 + c1) / 3
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) →
    (∀ {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2), let p1 := (u1 + c1) / 2
  let p2 := (u2 + c2) / 2
  let r1 := ((u1 - c1) ^ 2) / (4 * u1)
  let r2 := ((u2 - c2) ^ 2) / (4 * u2)
  p1 = (u1 + c1) / 2 ∧ p2 = (u2 + c2) / 2 ∧
  r1 = ((u1 - c1) ^ 2) / (4 * u1) ∧ r2 = ((u2 - c2) ^ 2) / (4 * u2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    (0 < c2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c1 : ℝ) (c2 : ℝ) (u1 : ℝ) (u2 : ℝ), (0 < c1) ∧ (0 < u1) ∧ (0 < u2) ∧ (¬((0 < c2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c2 : ℝ), ¬((0 < c2) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c2 : ℝ), ¬((0 < c2) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c2 : ℝ), ¬((0 < c2) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c2 : ℝ), ¬((0 < c2) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c2 : ℝ), ¬((0 < c2) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c2 : ℝ), ¬((0 < c2) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {c1 c2 u1 u2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
