import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (0 ≤ m₁) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (0 ≤ m₁)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (0 ≤ m₁)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (0 ≤ m₁)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (0 ≤ m₁)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (0 ≤ m₁)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (0 ≤ m₁)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (m₁ > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₂ : 0 < m₂) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁' : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁' : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁' : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁' : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁' : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : ¬(m₁ ≤ 0)) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) :
    (0 < m₁) ↔ (¬(m₁ ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : ¬(m₁ ≤ 0)) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : ¬(m₁ ≤ 0)) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : ¬(m₁ ≤ 0)) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) ↔
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : ¬(m₁ ≤ 0)) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ ≥ 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₁) ↔ (m₁ ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (m₁ ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (m₁ ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (m₁ ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (m₁ ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (m₁ ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ), ¬((0 < m₁) ↔ (m₁ ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ < M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (m₁ ≤ M₁) ↔ (m₁ < M₁) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₁ : ℝ) (M₁ : ℝ), ¬((m₁ ≤ M₁) ↔ (m₁ < M₁)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : m₁ > 0) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 5) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) →
    (∀ {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (a b : Fin n → ℝ) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂), (∑ i, a i ^ 2) * (∑ i, b i ^ 2) / (∑ i, a i * b i) ^ 2 ≤
    (1 / 4) * (Real.sqrt ((M₁ * M₂) / (m₁ * m₂)) + Real.sqrt ((m₁ * m₂) / (M₁ * M₂))) ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    (0 < m₂) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m₂ : ℝ), ¬((0 < m₂) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₂ : ℝ), ¬((0 < m₂) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₂ : ℝ), ¬((0 < m₂) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₂ : ℝ), ¬((0 < m₂) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₂ : ℝ), ¬((0 < m₂) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m₂ : ℝ), ¬((0 < m₂) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {m₁ m₂ M₁ M₂ : ℝ} (a b : Fin n → ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) (ha : ∀ i, m₁ ≤ a i ∧ a i ≤ M₁) (hb : ∀ i, m₂ ≤ b i ∧ b i ≤ M₂) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
