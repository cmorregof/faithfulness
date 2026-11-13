import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 698

*References:*
- [erdosproblems.com/698](https://www.erdosproblems.com/698)
- [ErSz78] Erdős, P. and Szekeres, G., *Some number theoretic problems on binomial
  coefficients*. Austral. Math. Soc. Gaz. (1978), 97-99.
- [Be11] Bergman, George M., *On common divisors of multinomial coefficients*. Bull. Aust.
  Math. Soc. (2011), 138--157.
-/

section

namespace Erdos698

open Filter

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

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
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (1 < i) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(2 : ℕ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (1 < i))) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

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
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(2 : ℕ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ))) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (i ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hij : i < j) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hij : i < j) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hij : i < j) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hij : i < j) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hij : i < j) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    ((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) ∧ (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi₀ : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi₀ : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi₀ : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi₀ : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi₀ : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : ¬(i < 1)) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : ¬(i < 1)) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : ¬(i < 1)) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : ¬(i < 1)) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : ¬(i < 1)) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) :
    (1 ≤ i) ↔ (0 < i) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i ≤ j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (i ≤ j) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (i ≤ j))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (i ≤ j)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i > 1) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hij : i < j) (hj : j ≤ n / 2) :
    (1 ≤ i) ↔ (i > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (i < j) ∧ (j ≤ n / 2) ∧ (¬((1 ≤ i) ↔ (i > 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

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
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : i ≥ 1) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j < n / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j < n / 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j < n / 2)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j ≤ n / 3), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    (j ≤ n / 2) ↔ (j ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (i < j) ∧ (¬((j ≤ n / 2) ↔ (j ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (j : ℕ), ¬((j ≤ n / 2) ↔ (j ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ n / 2) :
    (i < j) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), (1 ≤ i) ∧ (j ≤ n / 2) ∧ (¬((i < j) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ) (j : ℕ), ¬((i < j) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) →
    (∀ (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2), (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(2 : ℕ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (i : ℕ) (j : ℕ), ¬(((n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ)) ↔ ((2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ))) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
