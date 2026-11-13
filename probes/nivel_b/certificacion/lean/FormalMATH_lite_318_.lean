import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (0 < x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x ≤ 110) ↔ (110 ≥ x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) (hx : x > 0), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) (hx : x > 0), x ≤ 110) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) (hx : x > 0), x ≤ 110) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) (hx : x > 0), x ≤ 110) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) (hx : x > 0), x ≤ 110) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx₀ : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx₀ : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx₀ : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx₀ : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx₀ : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : ¬(x ≤ 0)) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x : ℝ) :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : ¬(x ≤ 0)) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : ¬(x ≤ 0)) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : ¬(x ≤ 0)) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) ↔
    (∀ (x : ℝ) (hx : ¬(x ≤ 0)) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x < 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x < 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x < 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 ≤ x) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (0 ≤ x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (0 ≤ x))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (0 ≤ x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (0 ≤ x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (0 ≤ x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (0 ≤ x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (0 ≤ x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (0 ≤ x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 31 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : 0 < x) (h : 30 + 0.4 * (x - 60) < 50), x ≥ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(x ≥ 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (x ≥ 110)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 > x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 > x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 > x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x ≥ 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (h : 30 + 0.4 * (x - 60) < 50) :
    (x > 0) ↔ (x ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (30 + 0.4 * (x - 60) < 50) ∧ (¬((x > 0) ↔ (x ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x > 0) ↔ (x ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 31 + 0.4 * (x - 60) < 50), 110 ≥ x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (31 + 0.4 * (x - 60) < 50)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), 110 ≤ x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (30 + 0.4 * (x - 60) < 50) ∧ (¬(110 ≤ x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(110 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(109 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(111 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((x ≤ 110) ↔ (110 ≤ x)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x : ℝ) (hx : x > 0), x ≤ 110

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x : ℝ) (hx : x > 0), x ≤ 110) →
    (∀ (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50), x ≤ 110) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) :
    (30 + 0.4 * (x - 60) < 50) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), (x > 0) ∧ (¬((30 + 0.4 * (x - 60) < 50) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(60 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(59 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(61 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(51 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ), ¬((30 + 0.4 * (x - 60) < 50) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x : ℝ) (hx : x > 0) (h : 30 + 0.4 * (x - 60) < 50) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
