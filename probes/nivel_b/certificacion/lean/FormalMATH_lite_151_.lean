import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Finset Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (True) := by
  plausible

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
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n ≤ 0)) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : n > 0) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 < x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) :
    (∀ i ∈ Icc 1 n, 1 ≤ x i) ↔ (∀ i ∈ Icc 1 n, 1 < x i) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) →
    (∀ {n : ℕ} (hn : 1 < n) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i), (∏ i ∈ Icc 1 n, (x i - 1)) / (∑ i ∈ Icc 1 n, (x i - 1))^n ≤
    (∏ i ∈ Icc 1 n, x i) / (∑ i ∈ Icc 1 n, x i)^n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    (0 < n) ↔ (1 < n) := by
  plausible

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
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (x : ℕ → ℝ) (hn : 0 < n) (hx : ∀ i ∈ Icc 1 n, 1 ≤ x i) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
