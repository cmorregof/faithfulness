import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≤ y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (x ≤ y) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (y > x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hy : y < 0) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hy : y < 0) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hy : y < 0) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hy : y < 0) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hy : y < 0) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx₀ : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx₀ : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx₀ : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx₀ : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx₀ : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : ¬(y ≤ x)) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x < y) ↔ (¬(y ≤ x)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : ¬(y ≤ x)) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : ¬(y ≤ x)) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : ¬(y ≤ x)) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔
    (∀ (x y : ℝ) (hx : ¬(y ≤ x)) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y ≥ x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : y < 0) :
    (x < y) ↔ (y ≥ x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (y < 0) ∧ (¬((x < y) ↔ (y ≥ x))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x < y) ↔ (y ≥ x)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : y > x) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (y < 0) ∧ (¬(Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) ↔ (Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -3 * x)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x < y), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) →
    (∀ (x y : ℝ) (hx : x < y) (hy : y < 0), Real.sqrt ((x - y)^2) + Real.sqrt ((x + y)^2) = -2 * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) :
    (y < 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x < y) ∧ (¬((y < 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y < 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y < 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y < 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y < 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y < 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y < 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) (hy : y < 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) (hy : y < 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) (hy : y < 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) (hy : y < 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x < y) (hy : y < 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
