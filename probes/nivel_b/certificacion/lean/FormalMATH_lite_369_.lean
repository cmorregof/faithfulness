import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    (L > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ∧ (¬((L > 0) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((L > 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((L > 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((L > 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((L > 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((L > 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((L > 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  omega

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  omega

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (0 < L) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) (h₀ : L > 0), L = 42

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) (h₀ : L > 0), L = 42) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) (h₀ : L > 0), L = 42) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) (h₀ : L > 0), L = 42) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) (h₀ : L > 0), L = 42) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀' : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀' : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀' : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀' : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀' : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : ¬(L ≤ 0)) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (L : ℝ) :
    (L > 0) ↔ (¬(L ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : ¬(L ≤ 0)) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : ¬(L ≤ 0)) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : ¬(L ≤ 0)) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) ↔
    (∀ (L : ℝ) (h₀ : ¬(L ≤ 0)) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) →
    (∀ (L : ℝ) (h₀ : 0 < L) (h₁ : 6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)), L = 42) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  omega

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) :
    (6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), (L > 0) ∧ (¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(30 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(29 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(31 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(32 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (L : ℝ), ¬((6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) ↔ (6 * 31^2 = 2 * (20 * 30 + 30 * L + L * 20))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (L : ℝ) (h₀ : L > 0) (h₁ : 6 * 30^2 = 2 * (20 * 30 + 30 * L + L * 20)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
