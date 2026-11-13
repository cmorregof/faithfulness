import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : x > 0) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : x > 0) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : x > 0) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : x > 0) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : x > 0) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hy : 0 < y) (hx : 0 < x) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hy : 0 < y) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hy : 0 < y) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hy : 0 < y) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hy : 0 < y) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx₀ : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx₀ : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx₀ : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx₀ : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx₀ : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : ¬(x ≤ 0)) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : ¬(x ≤ 0)) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : ¬(x ≤ 0)) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : ¬(x ≤ 0)) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : ¬(x ≤ 0)) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 1 ≤ x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) :
    (0 < x) ↔ (1 ≤ x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : 1 ≤ x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : 1 ≤ x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : 1 ≤ x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) ↔
    (∀ (x y : ℕ) (hx : 1 ≤ x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 1 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hy : 0 < y) (hxy : x - y = 1) :
    (0 < x) ↔ (1 < x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < y) ∧ (x - y = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1), x = y + 1) →
    (∀ (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1), x = y + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hxy : x - y = 1) :
    (0 < y) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), (0 < x) ∧ (x - y = 1) ∧ (¬((0 < y) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℕ), ¬((0 < y) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℕ), ¬((0 < y) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℕ), ¬((0 < y) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℕ), ¬((0 < y) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℕ), ¬((0 < y) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℕ), ¬((0 < y) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x - y = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
