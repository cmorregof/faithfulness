import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(79999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2202 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(119999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(199 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(10 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(79999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2199 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(119999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(199 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(10 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2202 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (t ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht₀ : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht₀ : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht₀ : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht₀ : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht₀ : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : ¬(t < 0)), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : ¬(t < 0)), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : ¬(t < 0)), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : ¬(t < 0)), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔
    (∀ (t : ℝ) (ht : ¬(t < 0)), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht : 0 ≤ t), 80000 + 2200 * t = 120000 ↔ t = 200 / 11) →
    (∀ (t : ℝ) (ht : t ≥ 0), 80000 + 2201 * t = 120000 ↔ t = 200 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(79999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2202 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(119999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(199 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(10 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(79999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(80001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2199 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120000 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(119999 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(120001 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(200 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(199 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(201 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(11 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(10 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(12 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2202 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((80000 + 2200 * t = 120000 ↔ t = 200 / 11) ↔ (80000 + 2201 * t = 120000 ↔ t = 200 / 11)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht : 0 ≤ t) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht : 0 ≤ t) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht : 0 ≤ t) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht : 0 ≤ t) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht : 0 ≤ t) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
