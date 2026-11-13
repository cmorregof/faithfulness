import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (1 < a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf₀ : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf₀ : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : ¬(a ≤ 1)), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : ¬(a ≤ 1)), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : ¬(a ≤ 1)), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : ¬(a ≤ 1)), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) ↔
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : ¬(a ≤ 1)), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x ≥ 0) (a : ℝ) (ha : 1 < a), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (ha : a > 1) :
    (∀ x ∈ Set.Ioi 0, f x > 0) ↔ (∀ x ∈ Set.Ioi 0, f x ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℝ → ℝ} (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (a : ℝ), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) →
    (∀ {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (a : ℝ) (ha : a > 1), liminf (λ x => (deriv f x) / (f x)^a) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) :
    (a > 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℝ), ¬((a > 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (ha : a > 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (ha : a > 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (ha : a > 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (ha : a > 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℝ → ℝ} (a : ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) (hpos : ∀ x ∈ Set.Ioi 0, f x > 0) (ha : a > 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
