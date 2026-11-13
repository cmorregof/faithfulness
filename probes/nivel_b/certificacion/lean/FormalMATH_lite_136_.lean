import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Matrix Set
open scoped BigOperators

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A₁ : Matrix (Fin n) (Fin n) ℝ, k = rank A₁ ∧
      (∀ i, A₁ i i = 0) ∧ (∀ i j, i ≠ j → 0 < A₁ i j)} 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n ≤ 0)), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : n > 0), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) →
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) →
    (∀ {n : ℕ} (hn : 1 ≤ n), IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 3) ↔ (IsLeast {k | ∃ A : Matrix (Fin n) (Fin n) ℝ, k = rank A ∧
      (∀ i, A i i = 0) ∧ (∀ i j, i ≠ j → 0 < A i j)} 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
