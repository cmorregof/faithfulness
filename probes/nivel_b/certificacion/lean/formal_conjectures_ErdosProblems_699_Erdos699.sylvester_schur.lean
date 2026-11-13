import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 699

*Reference:* [erdosproblems.com/699](https://www.erdosproblems.com/699)
-/

section

namespace Erdos699

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p₁ : ℕ, p₁.Prime ∧ i < p₁ ∧ p₁ ∣ Nat.choose n i) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi_half : i ≤ n / 2) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi_half : i ≤ n / 2) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi₀ : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi₀ : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi₀ : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi₀ : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi₀ : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : ¬(i < 1)) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : ¬(i < 1)) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : ¬(i < 1)) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : ¬(i < 1)) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : ¬(i < 1)) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i > 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi_half : i ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (i ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : i ≥ 1) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i < n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i < n / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i < n / 2))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i < n / 2)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 3), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (i ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (i ≤ n / 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (i ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 0 < i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (i ≤ n / 2) ∧ (¬(∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) ↔ (∃ p : ℕ, p.Prime ∧ i > p ∧ p ∣ Nat.choose n i)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i : ℕ) (hi : 1 ≤ i), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) →
    (∀ (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2), ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) :
    (i ≤ n / 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), (1 ≤ i) ∧ (¬((i ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ), ¬((i ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
