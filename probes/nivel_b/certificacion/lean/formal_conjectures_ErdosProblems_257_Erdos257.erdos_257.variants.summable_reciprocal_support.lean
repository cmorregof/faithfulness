import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 257

*Reference:* [erdosproblems.com/257](https://www.erdosproblems.com/257)
-/

section

namespace Erdos257

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (2 < b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 3 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hb : 2 ≤ b) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hb : 2 ≤ b) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hb : 2 ≤ b) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hb : 2 ≤ b) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hb : 2 ≤ b) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb₀ : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb₀ : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb₀ : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb₀ : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb₀ : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : ¬(b < 2)) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : ¬(b < 2)) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : ¬(b < 2)) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : ¬(b < 2)) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : ¬(b < 2)) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 1 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) :
    (2 ≤ b) ↔ (1 < b) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) ↔
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 < b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b > 2) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : b ≥ 3) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (b ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (A : Set ℕ) (hb : 1 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) →
    (∀ (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)), Irrational (∑' n : A, 1 / ((b : ℝ) ^ (n : ℕ) - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite) (hsum : Summable fun a : A => 1 / (a : ℝ)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
