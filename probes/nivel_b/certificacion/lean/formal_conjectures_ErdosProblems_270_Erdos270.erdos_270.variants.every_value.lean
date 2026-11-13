import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 270

*References:*
- [erdosproblems.com/270](https://www.erdosproblems.com/270)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ha75] Hansen, E. R., *A Table of Series and Products*. Prentice-Hall (1975), 87.
- [CrKo25] T. Crmarić and V. Kovač, *On the irrationality of certain super-polynomially decaying
  series*. arXiv:2504.18712 (2025).
- [Ko26] V. Kovač, [solution of the linear case](https://www.erdosproblems.com/forum/thread/270#post-7469)
  (2026).
-/

section

open Filter

namespace Erdos270

/-- The series $\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$, indexed from $0$. -/
noncomputable def series (f : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (0 ≤ α) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α > 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : α > 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : α > 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : α > 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : α > 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔ (∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : 0 < α), ∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : 0 < α), ∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : 0 < α), ∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : 0 < α), ∃ f₁ : ℕ → ℕ, Tendsto f₁ atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f₁ (n + 1)), (i : ℝ))⁻¹) α) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα₀ : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : ¬(α ≤ 0)), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) →
    (∀ (α : ℝ) (hα : 0 < α), ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (0 < α) ↔ (α ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
