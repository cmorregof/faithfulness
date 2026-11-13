import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

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
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (0 ≤ x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (0 ≤ x))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

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
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hy : 0 < y) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hy : 0 < y) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hy : 0 < y) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hy : 0 < y) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hy : 0 < y) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx₀ : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx₀ : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx₀ : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx₀ : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx₀ : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : ¬(x ≤ 0)) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : ¬(x ≤ 0)) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : ¬(x ≤ 0)) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : ¬(x ≤ 0)) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) ↔
    (∀ (x y : ℝ) (hx : ¬(x ≤ 0)) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x ≥ 0) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hy : 0 < y) :
    (0 < x) ↔ (x ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < y) ∧ (¬((0 < x) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

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
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : x > 0) (hy : 0 < y), log (x^4 * y) = 5 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (0 < y) ∧ (¬(log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(0 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(5 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((log (x^4 * y) = 4 * log x + log y) ↔ (log (x^4 * y) = 5 * log x + log y)) :=
  ⟨(6 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : 0 < x), log (x^4 * y) = 4 * log x + log y) →
    (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), log (x^4 * y) = 4 * log x + log y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) :
    (0 < y) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (0 < x) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

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
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
