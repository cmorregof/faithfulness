import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx_pos : 0 < x), x = 12500 ∧ y = 10500) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    (True) ↔ (0 < x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23001 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23001 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(4 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23001 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(4 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(3 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23001 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(4 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(3 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(5 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23001 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(3 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(5 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(100 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23000 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(22999 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(23001 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (4 / 100 * x + 2 / 100 * y = 710) ∧ (¬((True) ↔ (0 < x))) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((True) ↔ (0 < x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((True) ↔ (0 < x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((True) ↔ (0 < x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((True) ↔ (0 < x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((True) ↔ (0 < x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((True) ↔ (0 < x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12501 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12501 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10500 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12501 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10500 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10499 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (10501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12501 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10500 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10499 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10501 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (10501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12501 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10500 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10499 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10501 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(0 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12500 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12499 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(12501 : ℝ), (10501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (x = 12500)) :=
  ⟨(10500 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 5 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) :
    (4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23001 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23001 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(4 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23001 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(4 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(3 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23001 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(4 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(3 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(5 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23001 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(3 : ℝ), (23001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(5 : ℝ), (22999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(100 : ℝ), (23000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23000 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(22999 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(23001 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), (x + y = 23000) ∧ (¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710))) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(5 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(5 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(100 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(5 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(100 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(99 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (101 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(5 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(100 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(99 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(101 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (101 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(5 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(100 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(99 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(101 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(2 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(5 : ℝ), (101 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((4 / 100 * x + 2 / 100 * y = 710) ↔ (5 / 100 * x + 2 / 100 * y = 710)) :=
  ⟨(100 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx : x + y = 23000), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx : x + y = 23000), x = 12500 ∧ y = 10500) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx : x + y = 23000), x = 12500 ∧ y = 10500) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx : x + y = 23000), x = 12500 ∧ y = 10500) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hy : 4 / 100 * x + 2 / 100 * y = 710) (hx : x + y = 23000), x = 12500 ∧ y = 10500) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500 ∧ x = 12500

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) :
    (x = 12500 ∧ y = 10500) ↔ (y = 10500 ∧ x = 12500) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500 ∧ x = 12500) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500 ∧ x = 12500) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500 ∧ x = 12500) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500 ∧ x = 12500) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx₀ : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx₀ : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx₀ : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx₀ : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) ↔
    (∀ (x y : ℝ) (hx₀ : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), x = 12500 ∧ y = 10500) →
    (∀ (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710), y = 10500) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12501 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12501 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10500 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12501 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10500 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10499 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (10501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12501 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10500 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10499 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10501 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (10501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12501 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10500 : ℝ), (10500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10499 : ℝ), (12501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10501 : ℝ), (12499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(0 : ℝ), (12500 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12500 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12499 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(12501 : ℝ), (10501 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 12500 ∧ y = 10500) ↔ (y = 10500)) :=
  ⟨(10500 : ℝ), (10499 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℝ) (hx : x + y = 23000) (hy : 4 / 100 * x + 2 / 100 * y = 710) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
