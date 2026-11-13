import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set
open scoped Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (3 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ)  :
    (x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ∈ Icc 0 (2 * π)) ↔ (x ∈ Icc 0 (3 * π))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ∧ 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx₀ : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx₀ : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx₀ : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx₀ : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔
    (∀ (x : ℝ) (hx₀ : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), 2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) →
    (∀ (x : ℝ) (hx : x ∈ Icc 0 (2 * π)), abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2) ↔ (abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x ∈ Icc 0 (2 * π)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x ∈ Icc 0 (2 * π)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x ∈ Icc 0 (2 * π)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x ∈ Icc 0 (2 * π)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x ∈ Icc 0 (2 * π)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
