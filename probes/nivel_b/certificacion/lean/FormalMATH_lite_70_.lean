import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Set

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β ≥ 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (α * β ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (α * β ≥ 0))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (α * β ≥ 0)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : 0 < α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (0 < α * β) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : 0 < α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : 0 < α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : 0 < α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : 0 < α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔ ({a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n₁, x (n₁ + 1) = (x n₁ + α) / (β * x n₁ + 1)} =
    {a | a = sqrt (α / β)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ₀ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ₀ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ₀ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ₀ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ₀ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : ¬(α * β ≤ 0)), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) :
    (α * β > 0) ↔ (¬(α * β ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : ¬(α * β ≤ 0)), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : ¬(α * β ≤ 0)), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : ¬(α * β ≤ 0)), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) ↔
    (∀ (α β : ℝ) (hαβ : ¬(α * β ≤ 0)), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α β : ℝ) (hαβ : 0 ≤ α * β), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) →
    (∀ (α β : ℝ) (hαβ : α * β > 0), {a | ¬∃ (x : ℕ → ℝ), x 0 = a ∧ ∀ n, x (n + 1) = (x n + α) / (β * x n + 1)} =
    {a | a = sqrt (α / β)}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  omega

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α β : ℝ)  :
    (α * β > 0) ↔ (0 ≤ α * β) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), (¬((α * β > 0) ↔ (0 ≤ α * β))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ) (β : ℝ), ¬((α * β > 0) ↔ (0 ≤ α * β)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α β : ℝ) (hαβ : α * β > 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α β : ℝ) (hαβ : α * β > 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α β : ℝ) (hαβ : α * β > 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α β : ℝ) (hαβ : α * β > 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α β : ℝ) (hαβ : α * β > 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
