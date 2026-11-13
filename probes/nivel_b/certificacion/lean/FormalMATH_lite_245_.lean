import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Filter Real Function
open scoped BigOperators Topology

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α ≥ 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (α ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (α ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (α ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (α ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (α ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (α ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (α ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (0 < α) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    ((α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔ ((α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L₁, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L₁))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀' : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀' : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀' : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀' : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀' : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : ¬(α ≤ 0)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) :
    (α > 0) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : ¬(α ≤ 0)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : ¬(α ≤ 0)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : ¬(α ≤ 0)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) ↔
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : ¬(α ≤ 0)), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 ≤ α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (0 ≤ α) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (0 ≤ α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (0 ≤ α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (0 ≤ α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (0 ≤ α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (0 ≤ α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (0 ≤ α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 < a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : 0 < α), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    (∀ n, 0 ≤ a n) ↔ (∀ n, 0 < a n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₀ : ∀ n, 0 ≤ a n), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) →
    (∀ {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0), (α > 1 → ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L)) ∧
  (0 < α ∧ α ≤ 1 → ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i / (∑ j in Finset.Icc 1 i, a j) ^ α)) atTop (𝓝 L))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) :
    (α > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α > 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {α : ℝ} (a : ℕ → ℝ) (h₀ : ∀ n, 0 ≤ a n) (h₁ : ¬ ∃ L, Tendsto (λ n => (∑ i in Finset.Icc 1 n, a i)) atTop (𝓝 L)) (h₂ : α > 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
