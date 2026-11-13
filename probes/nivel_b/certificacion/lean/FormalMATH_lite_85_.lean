import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : n > 0) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ)  :
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
  ∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/3) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) →
    (∀ (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℝ), (∑ i : Fin n, (a i)^3)^((1 : ℝ)/4) ≤
    (∑ i : Fin n, (a i)^2)^((1 : ℝ)/2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (a : Fin n → ℝ) (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
