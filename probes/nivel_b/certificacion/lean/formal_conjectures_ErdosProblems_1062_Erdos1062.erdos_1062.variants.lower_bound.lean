import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1062

*Reference:* [erdosproblems.com/1062](https://www.erdosproblems.com/1062)
-/

section

open Filter
open scoped Topology

namespace Erdos1062

/-- A set `A` of positive integers is fork-free if no element divides two distinct
other elements of `A`. -/
def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

/-- The extremal function from Erdős problem 1062: the largest size of a fork-free subset of
`{1,...,n}`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

-- TODO: Add erdos_1062.parts.i: How large can $f(n)$ be?

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ < f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ < f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(3 * n / 3 : ℝ)⌉₊ ≤ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (⌈(2 * n / 3 : ℝ)⌉₊ ≥ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < ⌈(2 * n / 3 : ℝ)⌉₊)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n > ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≥ ⌈(3 * n / 3 : ℝ)⌉₊)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) →
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) →
    (∀ (n : ℕ), f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n) ↔ (f n ≤ ⌈(2 * n / 3 : ℝ)⌉₊)) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
