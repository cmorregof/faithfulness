import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Hall's conjecture

There exists a positive number $C$ such that for any integer $x, y$ with $y^2 \ne x^3$,
$|y^2 - x^3| > C \sqrt{|x|}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hall%27s_conjecture)
- L. Danilov, *The Diophantine equation $x^3 - y^2 = k$ and Hall's conjecture*, Mathematical notes of the Academy of Sciences of the USSR 32 (1982): 617-618
-/

section

open Real

namespace Hall
def HallIneq (C : ℝ) (e : ℝ) : Prop :=
  ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 → |y ^ 2 - x ^ 3| > C * (|x| : ℝ) ^ e
def HallConjectureExp (e : ℝ) : Prop := ∃ C : ℝ, C > 0 ∧ HallIneq C e

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ ≥ 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (δ ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (δ ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (δ ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (δ ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (δ ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (δ ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (δ ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (δ ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (δ ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (δ ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (δ ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (δ ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (δ ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  omega

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (0 < δ) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h₀ : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h₀ : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h₀ : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h₀ : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h₀ : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : ¬(δ ≤ 0)), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (δ : ℝ) :
    (δ > 0) ↔ (¬(δ ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : ¬(δ ≤ 0)), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : ¬(δ ≤ 0)), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : ¬(δ ≤ 0)), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) ↔
    (∀ (δ : ℝ) (h : ¬(δ ≤ 0)), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 ≤ δ), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  omega

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  simp_all

set_option maxHeartbeats 200000 in
example (δ : ℝ)  :
    (δ > 0) ↔ (0 ≤ δ) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (0 ≤ δ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (0 ≤ δ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (0 ≤ δ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (0 ≤ δ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (0 ≤ δ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (¬((δ > 0) ↔ (0 ≤ δ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (0 ≤ δ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (0 ≤ δ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (0 ≤ δ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (0 ≤ δ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (0 ≤ δ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((δ > 0) ↔ (0 ≤ δ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (δ : ℝ) (h : δ > 0), ¬ HallConjectureExp (2⁻¹ + δ)) →
    (∀ (δ : ℝ) (h : 0 < δ), ¬ HallConjectureExp (3⁻¹ + δ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), (δ > 0) ∧ (¬(¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((¬ HallConjectureExp (2⁻¹ + δ)) ↔ (¬ HallConjectureExp (3⁻¹ + δ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (δ : ℝ) (h : δ > 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (δ : ℝ) (h : δ > 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (δ : ℝ) (h : δ > 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (δ : ℝ) (h : δ > 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (δ : ℝ) (h : δ > 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
