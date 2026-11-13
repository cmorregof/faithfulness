import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 384

*References:*
- [erdosproblems.com/384](https://www.erdosproblems.com/384)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ec69] Ecklund, Jr., E. F., *On prime divisors of the binomial coefficient*. Pacific J. Math.
  (1969), 267-270.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
-/

section

namespace Erdos384

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(4 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(9 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ n.choose k ∧ 2 * p₁ ≤ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hkn : k < n - 1) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hkn : k < n - 1) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hkn : k < n - 1) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hkn : k < n - 1) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hkn : k < n - 1) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk₀ : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk₀ : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk₀ : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk₀ : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk₀ : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : ¬(k ≤ 1)) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : ¬(k ≤ 1)) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : ¬(k ≤ 1)) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : ¬(k ≤ 1)) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : ¬(k ≤ 1)) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k ≥ 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (k ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (8, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₄ : (n, k) ≠ (7, 4)) :
    ((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3)))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(4 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(9 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(6 : ℕ), (9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(8 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬(((n, k) ≠ (7, 3)) ↔ ((n, k) ≠ (8, 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : k > 1) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p < n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (k ≤ n - 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (k ≤ n - 1))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (k ≤ n - 1)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (1 < k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (k < n - 1) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬(∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) ↔ (∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≥ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) →
    (∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)), ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    (k < n - 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(2 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(7 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(8 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(7 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(8 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(2 : ℕ), (8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ ((n, k) ≠ (7, 3)) ∧ ((n, k) ≠ (7, 4)) ∧ (¬((k < n - 1) ↔ (True))) :=
  ⟨(7 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k < n - 1) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3)) (h₄ : (n, k) ≠ (7, 4)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
